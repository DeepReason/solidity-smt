import {
  AccessibleSolidityExprType,
  ContractSolidityExpr,
  MappingSolidityExpr,
  SolidityExpr,
  SolidityExprType,
  TranslationContext,
  TypeSolidityExpr,
} from './sharedTypes';
import {
  ContractTypeObject,
  elementaryTypeNameToByte,
  EnumTypeObject,
  isSameSolidityType,
  makeElementarySolidityType,
  StructTypeObject,
  VarTypeKind,
} from '../sol_parsing';
import { makeZ3Balances, makeZ3GlobalStorage } from './solidityZ3Generator';
import { BitVec } from '../z3/z3';
import assert from 'assert';
import { UserDefinedTypeKind } from '../sol_parsing/sol_parsing_types';
import { Bool } from 'z3-solver';
import { Mutability } from 'solc-typed-ast';

export function getDefaultContractExpr(ctx: TranslationContext): ContractSolidityExpr {
  const contractId = ctx.parsedSolidityData.contractId[ctx.contractName];
  const contractAddress = ctx.exposedImmutables.deploymentAddresses[ctx.contractName] as BitVec<160>;
  return {
    type: SolidityExprType.ACCESSIBLE,
    accessibleType: AccessibleSolidityExprType.CONTRACT,
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
  const im = ctx.exposedImmutables.exposedImmutables[ctx.contractName];
  if (accessible.type === SolidityExprType.ACCESSIBLE) {
    switch (accessible.accessibleType) {
      case AccessibleSolidityExprType.CONTRACT:
        const contractId = accessible.id;
        const contractData = ps.typeObjects[contractId];
        assert(contractData.type === 'Contract');
        return Object.keys(contractData.vars).concat(Object.keys(im[contractData.name]));
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

export function dotAccess(accessible: SolidityExpr, member: string, ctx: TranslationContext): SolidityExpr {
  const z3 = ctx.z3;
  if (accessible.type === SolidityExprType.ACCESSIBLE) {
    switch (accessible.accessibleType) {
      case AccessibleSolidityExprType.CONTRACT:
        const contract = ctx.parsedSolidityData.typeObjects[accessible.id];
        assert(contract.type === UserDefinedTypeKind.CONTRACT);
        assert(member in contract.vars);
        const varData = contract.vars[member];

        const slot = varData.slot.slot[0];

        const type = varData.type;
        if (varData.mutability !== Mutability.Mutable) {
          throw Error('Unimplemented: immutable storage access');
        }
        if (type.type == VarTypeKind.ElementaryTypeName) {
          let expr = makeZ3GlobalStorage(z3)
            .select(accessible.contractAddress)
            .select(z3.BitVec.val(slot, 256)) as BitVec;
          if (varData.slot.intraSlot) {
            const offset = varData.slot.intraSlot[0];
            const intraSlotEnd = offset + elementaryTypeNameToByte(type.name);
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
            contractAddress: accessible.contractAddress,
            slot: z3.BitVec.val(slot, 256),
          };
        } else if (type.type == VarTypeKind.ArrayTypeName) {
          return {
            type: SolidityExprType.ARRAY,
            varType: type,
            contractAddress: accessible.contractAddress,
            slot: z3.BitVec.val(slot, 256),
          };
        } else {
          throw Error('TODO');
        }
      case AccessibleSolidityExprType.STRUCT:
        throw Error('TODO');
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
        throw Error('TODO');
      case UserDefinedTypeKind.STRUCT:
        throw Error('TODO');
      case UserDefinedTypeKind.ENUM:
        throw Error('TODO');
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

  const inputBytes = elementaryTypeNameToByte(key.varType.name);
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
    const outputBytes = elementaryTypeNameToByte(outputType.name);
    let outputExpr = makeZ3GlobalStorage(z3).select(mapping.contractAddress).select(hash_val) as BitVec;
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
      slot: hash_val,
      varType: outputType,
    };
  } else if (outputType.type === VarTypeKind.ArrayTypeName) {
    return {
      type: SolidityExprType.ARRAY,
      contractAddress: mapping.contractAddress,
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
