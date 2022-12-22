import assert from 'assert';
import { ArrayTypeName, ElementaryTypeName, Mapping, TypeName, UserDefinedTypeName } from 'solc-typed-ast';
import { elementaryTypeNameToByte } from './var_parsing';
import { ElementaryVarType, UserDefinedVarType, VarType, VarTypeKind } from './sol_parsing_types';

export function makeElementaryVarType(name: string): ElementaryVarType {
  return {
    type: VarTypeKind.ElementaryTypeName,
    name,
    stateMutability: null,
  };
}

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
    const mappingTypeNames = typeName as Mapping;
    return {
      type: VarTypeKind.Mapping,
      keyType: typeNameToVarType(mappingTypeNames.vKeyType) as ElementaryVarType | UserDefinedVarType,
      valueType: typeNameToVarType(mappingTypeNames.vValueType),
    };
  }
  if (typeName.type === 'ArrayTypeName') {
    const arrayTypeName = typeName as ArrayTypeName;
    return {
      type: VarTypeKind.ArrayTypeName,
      baseType: typeNameToVarType(arrayTypeName.vBaseType),
      length: arrayTypeName.vLength,
    };
  }
  if (typeName.type === 'ElementaryTypeName') {
    const elementaryTypeName = typeName as ElementaryTypeName;
    return {
      type: VarTypeKind.ElementaryTypeName,
      name: elementaryTypeName.name,
      stateMutability: elementaryTypeName.stateMutability,
    };
  }
  if (typeName.type === 'UserDefinedTypeName') {
    const userDefinedTypeName = typeName as UserDefinedTypeName;
    return {
      type: VarTypeKind.UserDefinedTypeName,
      name: userDefinedTypeName.path!.name!,
    };
  }
  throw new Error('Unknown type: ' + typeName.type);
}
