import { TypeName } from '@solidity-parser/parser/src/ast-types';
import assert from 'assert';
import { elementaryTypeNameToByte } from './var_parsing';

export enum VarTypeKind {
  Mapping,
  ArrayTypeName,
  ElementaryTypeName,
  UserDefinedTypeName,
}

export type ElementaryVarType = {
  type: VarTypeKind.ElementaryTypeName;
  name: string;
  stateMutability: string | null;
};

export function makeElementaryVarType(name: string): ElementaryVarType {
  return {
    type: VarTypeKind.ElementaryTypeName,
    name,
    stateMutability: null,
  };
}

export type UserDefinedVarType = {
  type: VarTypeKind.UserDefinedTypeName;
  name: string;
};

export type ArrayVarType = {
  type: VarTypeKind.ArrayTypeName;
  baseType: VarType;
  length: any;
};

export type MappingVarType = {
  type: VarTypeKind.Mapping;
  keyType: ElementaryVarType | UserDefinedVarType;
  valueType: VarType;
};

// An abstraction around @solidity-parser/parser's TypeName but with more safety
export type VarType = ElementaryVarType | MappingVarType | ArrayVarType | UserDefinedVarType;

export function varTypeToString(varType: VarType): string {
  switch (varType.type) {
    case VarTypeKind.ElementaryTypeName:
      return varType.name;
    case VarTypeKind.Mapping:
      return `mapping(${varTypeToString(varType.keyType)} => ${varTypeToString(varType.valueType)})`;
    case VarTypeKind.ArrayTypeName:
      return `${varTypeToString(varType.baseType)}[]`;
    case VarTypeKind.UserDefinedTypeName:
      return varType.name;
    default:
      throw new Error('Unknown VarTypeKind');
  }
}

export function isSameType(varType1: VarType, varType2: VarType): boolean {
  if (varType1.type !== varType2.type) {
    return false;
  }
  switch (varType1.type) {
    case VarTypeKind.ElementaryTypeName:
      assert(varType2.type === VarTypeKind.ElementaryTypeName);
      const name1 = varType1.name;
      const name2 = varType2.name;
      if (name1.startsWith('uint') && name2.startsWith('uint')) {
        return elementaryTypeNameToByte(name1) === elementaryTypeNameToByte(name2);
      } else if (name1.startsWith('int') && name2.startsWith('int')) {
        return elementaryTypeNameToByte(name1) === elementaryTypeNameToByte(name2);
      }
      return name1 === name2;
    case VarTypeKind.Mapping:
      assert(varType2.type === VarTypeKind.Mapping);
      return isSameType(varType1.keyType, varType2.keyType) && isSameType(varType1.valueType, varType2.valueType);
    case VarTypeKind.ArrayTypeName:
      assert(varType2.type === VarTypeKind.ArrayTypeName);
      return isSameType(varType1.baseType, varType2.baseType);
    case VarTypeKind.UserDefinedTypeName:
      assert(varType2.type === VarTypeKind.UserDefinedTypeName);
      return varType1.name === varType2.name;
    default:
      throw new Error('Unknown VarTypeKind');
  }
}

export function typeNameToVarType(typeName: TypeName): VarType {
  if (typeName.type === 'Mapping') {
    return {
      type: VarTypeKind.Mapping,
      keyType: typeNameToVarType(typeName.keyType) as ElementaryVarType | UserDefinedVarType,
      valueType: typeNameToVarType(typeName.valueType),
    };
  }
  if (typeName.type === 'ArrayTypeName') {
    return {
      type: VarTypeKind.ArrayTypeName,
      baseType: typeNameToVarType(typeName.baseTypeName),
      length: typeName.length,
    };
  }
  if (typeName.type === 'ElementaryTypeName') {
    return {
      type: VarTypeKind.ElementaryTypeName,
      name: typeName.name,
      stateMutability: typeName.stateMutability,
    };
  }
  if (typeName.type === 'UserDefinedTypeName') {
    return {
      type: VarTypeKind.UserDefinedTypeName,
      name: typeName.namePath,
    };
  }
  throw new Error('Unknown type: ' + typeName.type);
}
