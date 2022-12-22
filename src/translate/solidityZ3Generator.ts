import { BitVec, BitVecSort, Expr, SMTArray, SMTArraySort, Z3Obj } from '../z3/z3';
import {
  ContractTypeObject,
  elementaryTypeNameToByte,
  ElementaryVarType,
  MappingVarType,
  ParsedSolidityData,
  VarType,
  VarTypeKind,
  varTypeToString,
} from '../sol_parsing';
import assert from 'assert';
import { AnySort, Bool, Sort, Z3_ast } from 'z3-solver';

export type Z3SolidityGenerators = {
  solidityData: ParsedSolidityData;
  globalVarZ3Generators: Map<string, AnnotatedZ3Generator>;
  warnings: string[];
};

export type GlobalStorageZ3 = SMTArray<
  'main',
  [BitVecSort<160>],
  SMTArraySort<'main', [BitVecSort<256>], BitVecSort<256>>
>;

export const makeZ3GlobalStorage = (z3: Z3Obj, tags: string = '') => {
  return z3.Array.const(
    'global_storage' + tags,
    z3.BitVec.sort(160),
    z3.Array.sort(z3.BitVec.sort(256), z3.BitVec.sort(256)),
  );
};

export const makeZ3Balances = (z3: Z3Obj, tags: string = '') => {
  return z3.Array.const('balances' + tags, z3.BitVec.sort(160), z3.BitVec.sort(256));
};

export type ASTExpr<Name extends string = 'main', S extends Sort<Name> = AnySort<Name>> = Expr<Name, S, Z3_ast>;

export type AnnotatedExpr = {
  solidityType: VarType;
  expr: ASTExpr;
};

export type AnnotatedMappingZ3 = {
  solidityType: MappingVarType;
  indexSort: Sort;
  get: (idx: Bool | BitVec) => AnnotatedMappingZ3 | AnnotatedExpr;
};

export function isAnnotatedZ3(expr: any): expr is AnnotatedExpr | AnnotatedMappingZ3 {
  return expr !== undefined && expr !== null && expr['solidityType'] !== undefined;
}

export function isAnnotatedZ3Expr(expr: any): expr is AnnotatedExpr {
  return isAnnotatedZ3(expr) && (expr as any)['expr'] !== undefined;
}

export function isAnnotatedZ3Mapping(expr: any): expr is AnnotatedMappingZ3 {
  return isAnnotatedZ3(expr) && (expr as any)['indexSort'] !== undefined;
}

export type AnnotatedZ3 = AnnotatedExpr | AnnotatedMappingZ3;

export type UnslottedZ3Generator = (slot: BitVec<256>, offset: number | undefined) => AnnotatedZ3;

export type AnnotatedExprGenerator = (z3: Z3Obj, globalStorage: GlobalStorageZ3) => AnnotatedExpr;
export type AnnotatedZ3Generator = (z3: Z3Obj, globalStorage: GlobalStorageZ3) => AnnotatedZ3;

export type StateVarUnslottedZ3Generator = (z3: Z3Obj, globalStorage: GlobalStorageZ3) => UnslottedZ3Generator;

function solidityElementaryVarToUnslottedZ3Generator(
  type: ElementaryVarType,
  contractName: string,
): StateVarUnslottedZ3Generator {
  return (z3: Z3Obj, globalStorage: GlobalStorageZ3) => {
    return (slot: BitVec<256>, offset: number | undefined) => {
      const Z3_contract_addr = z3.BitVec.const(contractName + '_addr', 160);
      let data = globalStorage.select(Z3_contract_addr).select(slot) as BitVec;
      if (offset !== undefined) {
        const intraSlotEnd = offset + elementaryTypeNameToByte(type.name);
        data = z3.Extract(255 - offset * 8, 256 - intraSlotEnd * 8, data);
      }
      return {
        solidityType: type,
        expr: data,
      };
    };
  };
}

function solidityMappingVarToUnslottedZ3Generator(
  type: MappingVarType,
  contractName: string,
): StateVarUnslottedZ3Generator {
  const keyType = type.keyType;
  const valueType = type.valueType;
  if (keyType.type !== VarTypeKind.ElementaryTypeName) {
    throw new Error('Unsupported: Mapping key type must be elementary');
  }

  assert(keyType.name !== 'string ' && keyType.name !== 'bytes');
  const inputBytes = elementaryTypeNameToByte(keyType.name);
  assert(inputBytes <= 32);

  const subcallUnslottedGenerator = solidityVarToUnslottedZ3Generator(valueType, contractName);

  return (z3: Z3Obj, global_storage: GlobalStorageZ3) => {
    const keccak = z3.Function.declare('keccak256_512', z3.BitVec.sort(512), z3.BitVec.sort(256));
    const indexSort = keyType.name === 'boolean' ? z3.Bool.sort() : z3.BitVec.sort(inputBytes * 8);
    return (slot: BitVec<256>, offset: number | undefined) => {
      assert(offset === undefined);
      const getFunction = (idx: Bool | BitVec) => {
        assert(idx.sort.eqIdentity(indexSort));
        if (idx.sort.eqIdentity(z3.Bool.sort())) {
          idx = z3.If(idx as Bool, z3.BitVec.val(1, 8), z3.BitVec.val(0, 8));
        }
        assert(z3.isBitVec(idx));
        const slotHalf0 =
          inputBytes == 32 ? idx : (z3.Concat(z3.BitVec.val(0, 256 - inputBytes * 8), idx) as BitVec<256>);
        const hash_input = z3.Concat(slotHalf0, slot) as BitVec<512>;
        const hash_val = keccak.call(hash_input);
        return subcallUnslottedGenerator(z3, global_storage)(hash_val, undefined);
      };
      return {
        solidityType: type,
        indexSort,
        get: getFunction,
      } as AnnotatedMappingZ3;
    };
  };
}

function solidityVarToUnslottedZ3Generator(type: VarType, contractName: string): StateVarUnslottedZ3Generator {
  switch (type.type) {
    case VarTypeKind.ElementaryTypeName:
      return solidityElementaryVarToUnslottedZ3Generator(type, contractName);
    case VarTypeKind.Mapping:
      return solidityMappingVarToUnslottedZ3Generator(type, contractName);
    default:
      throw new Error('Unsupported: Var type ' + varTypeToString(type));
  }
}

function getGlobalVarZ3Generator(
  solidityData: ParsedSolidityData,
  contract: string,
  warnings: string[],
): Map<string, AnnotatedZ3Generator> {
  const globalZ3Vars = new Map<string, AnnotatedZ3Generator>();

  const contractId = solidityData.contractId[contract];
  const contractData = solidityData.typeObjects[contractId] as ContractTypeObject;
  const contractVarData = contractData.vars;

  for (const [varName, contractVar] of Object.entries(contractVarData)) {
    try {
      const unslottedGenerator = solidityVarToUnslottedZ3Generator(contractVar.type, contract);
      assert(contractVar.slot !== undefined);
      if (contractVar.slot.slot[0] !== contractVar.slot.slot[1]) {
        throw new Error('Unsupported: Global vars must be in a single slot');
      }
      const generator = (z3: Z3Obj, global_storage: GlobalStorageZ3) => {
        const slot = z3.BitVec.val(contractVar.slot.slot[0], 256);
        return unslottedGenerator(z3, global_storage)(slot, contractVar.slot.intraSlot?.[0]);
      };
      globalZ3Vars.set(contractVar.name, generator);
    } catch (e: any) {
      warnings.push('' + e.message);
      warnings.push('Skipping global var: ' + contractVar.name);
    }
  }
  return globalZ3Vars;
}

export function solidityDataToZ3Generators(solidityData: ParsedSolidityData, contract: string): Z3SolidityGenerators {
  const warnings: string[] = [];
  const globalVarZ3Generators = getGlobalVarZ3Generator(solidityData, contract, warnings);
  return {
    solidityData,
    globalVarZ3Generators,
    warnings,
  };
}
