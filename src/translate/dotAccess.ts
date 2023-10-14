import {
  AccessibleSolidityExprType,
  ContractSolidityExpr,
  ElementarySolidityExpr,
  MappingSolidityExpr,
  SolidityExpr,
  SolidityExprType,
  TranslationContext,
  TypeSolidityExpr,
} from './sharedTypes';
import {
  ContractTypeObject,
  elementaryTypeNameToBytes,
  ElementaryVarType,
  EnumTypeObject,
  isSameSolidityType,
  makeElementarySolidityType,
  StructTypeObject,
  VarTypeKind,
} from '../sol_parsing';
import { makeZ3Balances, makeZ3Globals, makeZ3GlobalStorage } from './solidityZ3Generator';
import { BitVec } from '../z3/z3';
import assert from 'assert';
import { UserDefinedTypeKind } from '../sol_parsing/sol_parsing_types';
import { Expr } from 'z3-solver';
import { Mutability } from 'solc-typed-ast';
import { resizeZ3BitVec } from './valueType';
import { repr_of_expr } from '../z3';

export class UnimplementedError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'UnimplementedError';
  }
}

export function getDefaultContractExpr(ctx: TranslationContext): ContractSolidityExpr {
  const contractId = ctx.parsedSolidityData.contractId[ctx.contractName];
  const contractAddress = ctx.exposedImmutables.deploymentAddresses[ctx.contractName].main.address as BitVec<160>;
  return {
    type: SolidityExprType.ACCESSIBLE,
    accessibleType: AccessibleSolidityExprType.CONTRACT,
    globals: makeZ3Globals(ctx.z3),
    id: contractId,
    contractAddress,
  };
}

export function getDefaultContractTypeExpr(ctx: TranslationContext): TypeSolidityExpr {
  const contractId = ctx.parsedSolidityData.contractId[ctx.contractName];
  return {
    type: SolidityExprType.TYPE,
    typeType: UserDefinedTypeKind.CONTRACT,
    id: contractId,
  };
}

export function getTypeFromObjectId(objectId: number, ctx: TranslationContext): TypeSolidityExpr {
  const object = ctx.parsedSolidityData.typeObjects[objectId];
  return {
    type: SolidityExprType.TYPE,
    typeType: object.type,
    id: objectId,
  };
}

export function accessibleValues(accessible: SolidityExpr, ctx: TranslationContext): string[] {
  const ps = ctx.parsedSolidityData;
  if (accessible.type === SolidityExprType.ACCESSIBLE) {
    switch (accessible.accessibleType) {
      case AccessibleSolidityExprType.CONTRACT:
        const contractId = accessible.id;
        const contractData = ps.typeObjects[contractId];
        assert(contractData.type === 'Contract');
        return Object.keys(contractData.vars);
      case AccessibleSolidityExprType.STRUCT:
        const structId = accessible.id;
        const structData = ps.typeObjects[structId];
        assert(structData.type === 'Struct');
        return Object.keys(structData.vars);
      case AccessibleSolidityExprType.MESSAGE:
        return ['sender'];
    }
  } else if (accessible.type === SolidityExprType.TYPE) {
    switch (accessible.typeType) {
      case UserDefinedTypeKind.CONTRACT:
        const contractId = accessible.id;
        const contractData = ps.typeObjects[contractId] as ContractTypeObject;
        return Object.keys(contractData.subtypes);
      case UserDefinedTypeKind.STRUCT:
        const structId = accessible.id;
        const structData = ps.typeObjects[structId] as StructTypeObject;
        return Object.keys(structData.subtypes);
      case UserDefinedTypeKind.ENUM:
        const enumId = accessible.id;
        const enumData = ps.typeObjects[enumId] as EnumTypeObject;
        return Object.keys(enumData.values);
    }
  } else if (accessible.type === SolidityExprType.ELEMENTARY) {
    if (isSameSolidityType(accessible.varType, makeElementarySolidityType('address'))) {
      return ['balance'];
    }
  }
  return [];
}

export function castExprToElementarySolidityExpr(
  expr: Expr,
  varType: ElementaryVarType,
  ctx: TranslationContext,
): ElementarySolidityExpr {
  return {
    type: SolidityExprType.ELEMENTARY,
    varType,
    expr: expr.ctx.isBitVec(expr) ? resizeZ3BitVec(expr, elementaryTypeNameToBytes(varType.name) * 8) : expr,
  };
}

export function dotAccess(accessible: SolidityExpr, member: string, ctx: TranslationContext): SolidityExpr {
  const z3 = ctx.z3;
  if (accessible.type === SolidityExprType.ACCESSIBLE) {
    switch (accessible.accessibleType) {
      case AccessibleSolidityExprType.CONTRACT:
        const contract = ctx.parsedSolidityData.typeObjects[accessible.id];
        assert(contract.type === UserDefinedTypeKind.CONTRACT);
        if (!(member in contract.vars)) {
          throw new Error(`Member ${member} not found in type ${contract.name}`);
        }
        const varData = contract.vars[member];

        const slot = varData.slot.slot[0];

        const type = varData.type;
        if (varData.mutability === Mutability.Immutable) {
          const im = ctx.exposedImmutables;
          const imInfo = im.exposedImmutables[ctx.contractName][contract.name];
          assert(member in imInfo);
          const varInfo = imInfo[member];

          const addrHash = accessible.contractAddress.hash().toString();
          if (addrHash in varInfo) {
            const expr = varInfo[addrHash];
            if (type.type === VarTypeKind.ElementaryTypeName) {
              return castExprToElementarySolidityExpr(expr, type, ctx);
            } else if (type.type === VarTypeKind.UserDefinedTypeName) {
              const typeObj = ctx.parsedSolidityData.typeObjects[type.id];
              assert(typeObj !== undefined);
              if (typeObj.type === UserDefinedTypeKind.CONTRACT) {
                const z3 = ctx.z3;
                assert(z3.isBitVec(expr));
                return {
                  type: SolidityExprType.ACCESSIBLE,
                  accessibleType: AccessibleSolidityExprType.CONTRACT,
                  globals: accessible.globals,
                  id: type.id,
                  contractAddress: resizeZ3BitVec(expr, 160),
                };
              } else if (typeObj.type === UserDefinedTypeKind.STRUCT) {
                throw new UnimplementedError('Reading immutable structs');
              } else {
                throw new Error(`Reading immutable Enums`);
              }
            }
          } else {
            throw new Error('Could not decode the value of ' + member + ' in ' + accessible.ctx!.text);
          }
        } else if (varData.mutability === Mutability.Constant) {
          throw new UnimplementedError('Constant variables not supported');
        } else {
          if (type.type == VarTypeKind.ElementaryTypeName) {
            if (type.name === 'string' || type.name === 'bytes') {
              throw new UnimplementedError(`Type ${type.name} not supported`);
            }
            let expr = accessible.globals.storage
              .select(accessible.contractAddress)
              .select(z3.BitVec.val(slot, 256)) as BitVec;
            if (varData.slot.intraSlot) {
              const offset = varData.slot.intraSlot[0];
              const intraSlotEnd = offset + elementaryTypeNameToBytes(type.name);
              expr = z3.Extract(255 - offset * 8, 256 - intraSlotEnd * 8, expr);
            }
            return {
              type: SolidityExprType.ELEMENTARY,
              varType: type,
              expr,
            };
          } else if (type.type == VarTypeKind.Mapping) {
            return {
              type: SolidityExprType.MAPPING,
              varType: type,
              globals: accessible.globals,
              contractAddress: accessible.contractAddress,
              slot: z3.BitVec.val(slot, 256),
            };
          } else if (type.type == VarTypeKind.ArrayTypeName) {
            return {
              type: SolidityExprType.ARRAY,
              varType: type,
              globals: accessible.globals,
              contractAddress: accessible.contractAddress,
              slot: z3.BitVec.val(slot, 256),
            };
          } else {
            throw new UnimplementedError('Accessing user defined type variables in contracts');
          }
        }
      case AccessibleSolidityExprType.STRUCT:
        throw new UnimplementedError('Accessing structs');
      case AccessibleSolidityExprType.MESSAGE:
        if (member === 'sender') {
          return {
            type: SolidityExprType.ELEMENTARY,
            expr: z3.BitVec.const('sender', 160),
            varType: makeElementarySolidityType('address'),
          };
        }
        throw Error(`Field ${member} does not exist on msg`);
    }
  } else if (accessible.type === SolidityExprType.ELEMENTARY) {
    if (isSameSolidityType(accessible.varType, makeElementarySolidityType('address')) && member === 'balance') {
      const newExpr = makeZ3Balances(z3).select(accessible.expr as BitVec<160>);
      return {
        type: SolidityExprType.ELEMENTARY,
        expr: newExpr,
        varType: makeElementarySolidityType('uint256'),
      };
    }
  } else if (accessible.type === SolidityExprType.TYPE) {
    switch (accessible.typeType) {
      case UserDefinedTypeKind.CONTRACT:
        throw new UnimplementedError('accessing contract type');
      case UserDefinedTypeKind.STRUCT:
        throw new UnimplementedError('accessing struct type');
      case UserDefinedTypeKind.ENUM:
        throw new UnimplementedError('accessing enum type');
    }
  }
  throw new Error(accessible.ctx?.text + ' has no member ' + member);
}

export function mappingAccess(mapping: MappingSolidityExpr, key: SolidityExpr, ctx: TranslationContext): SolidityExpr {
  if (key.type !== SolidityExprType.ELEMENTARY) {
    throw Error(key.ctx!.text + ' is not a valid key for the mapping ' + mapping.ctx!.text);
  }
  if (!isSameSolidityType(key.varType, mapping.varType.keyType)) {
    throw Error(key.ctx!.text + ' is not a valid key for the mapping ' + mapping.ctx!.text);
  }

  const inputBytes = elementaryTypeNameToBytes(key.varType.name);
  const z3 = ctx.z3;

  const keccak = z3.Function.declare('keccak256_512', z3.BitVec.sort(512), z3.BitVec.sort(256));

  const slotHalf0: BitVec =
    inputBytes == 32
      ? (key.expr as BitVec)
      : (z3.Concat(z3.BitVec.val(0, 256 - inputBytes * 8), key.expr as BitVec) as BitVec<256>);
  const hash_input = z3.Concat(slotHalf0, mapping.slot as BitVec) as BitVec<512>;
  const hash_val = keccak.call(hash_input);

  const outputType = mapping.varType.valueType;
  if (outputType.type === VarTypeKind.ElementaryTypeName) {
    const outputBytes = elementaryTypeNameToBytes(outputType.name);
    let outputExpr = mapping.globals.storage.select(mapping.contractAddress).select(hash_val) as BitVec;
    if (outputBytes !== 32) {
      outputExpr = z3.Extract(outputBytes * 8 - 1, 0, outputExpr) as BitVec;
    }
    return {
      type: SolidityExprType.ELEMENTARY,
      expr: outputExpr,
      varType: outputType,
    };
  } else if (outputType.type === VarTypeKind.Mapping) {
    return {
      type: SolidityExprType.MAPPING,
      contractAddress: mapping.contractAddress,
      globals: mapping.globals,
      slot: hash_val,
      varType: outputType,
    };
  } else if (outputType.type === VarTypeKind.ArrayTypeName) {
    return {
      type: SolidityExprType.ARRAY,
      contractAddress: mapping.contractAddress,
      globals: mapping.globals,
      slot: hash_val,
      varType: outputType,
    };
  } else {
    assert(outputType.type === VarTypeKind.UserDefinedTypeName);
    throw Error('User defined types not supported');
    // return {
    //   type: SolidityExprType.TYPE,
    //   typeType: outputType,
    //   id: outputType.id,
    //   varType: outputType,
    // };
  }
}
