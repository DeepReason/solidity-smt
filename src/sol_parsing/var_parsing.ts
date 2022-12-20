import {
  ArrayTypeName,
  ElementaryTypeName,
  EnumDefinition,
  SourceUnit,
  StateVariableDeclarationVariable,
  StructDefinition,
  TypeName,
  UserDefinedTypeName,
  VariableDeclaration,
} from '@solidity-parser/parser/src/ast-types';
import { parse, ParserError } from '@solidity-parser/parser';
import { Token } from '@solidity-parser/parser/src/types';
import assert from 'assert';

type ParseResult = SourceUnit & {
  errors?: any[];
  tokens?: Token[];
};

export const parseSolidity = parse;
export type { ParserError, ParseResult };

export function typeNameToString(typeName: TypeName): string {
  if (typeName.type === 'Mapping') {
    return `mapping(${typeNameToString(typeName.keyType)} => ${typeNameToString(typeName.valueType)})`;
  }
  if (typeName.type === 'ArrayTypeName') {
    const base = typeNameToString((typeName as ArrayTypeName).baseTypeName);
    if (typeName.length) {
      return `${base}[${(typeName.length as any).number}]`;
    }
    return `${base}[]`;
  }
  if (typeName.type === 'ElementaryTypeName') {
    return (typeName as ElementaryTypeName).name;
  }
  if (typeName.type === 'UserDefinedTypeName') {
    return (typeName as UserDefinedTypeName).namePath;
  }
  return 'UNKNOWN';
}

export type UserTypeDefinition = StructDefinition | EnumDefinition;

function userTypeDefinitionToBytes(def: UserTypeDefinition, userTypeDefinitions: UserTypeDefinition[]): number {
  if (def.type === 'EnumDefinition') {
    const enumDefinition = def as EnumDefinition;
    const target = enumDefinition.members.length;
    let res = 8;
    while (1 << res < target) {
      res += 8;
    }
    return res / 8;
  } else {
    const structDefinition = def as StructDefinition;
    let bytes = 0;
    for (const variableDecl of structDefinition.members) {
      const newBytes = varDeclToBytes(variableDecl, userTypeDefinitions);
      const nextSlot = bytes % 32 === 0 ? bytes : (bytes & ~0x1f) + 32;
      if (bytes + newBytes <= nextSlot) {
        bytes += newBytes;
      } else {
        bytes = nextSlot + newBytes;
      }
    }
    if (bytes % 32 !== 0) {
      bytes &= ~0x1f;
      bytes += 32;
    }
    return bytes;
  }
}

export function stateVarDeclToBytes(
  varDecl: StateVariableDeclarationVariable,
  userTypeDefinitions: UserTypeDefinition[],
): number {
  if (varDecl.isImmutable) {
    return 0;
  }
  return varDeclToBytes(varDecl, userTypeDefinitions);
}

export function elementaryTypeNameToByte(name: string): number {
  if (name.startsWith('uint')) {
    const vStr = name.substring(4) || '256';
    const re = /^[1-9]\d*$/;
    if (!re.test(vStr)) {
      throw new Error('ERROR: Invalid uint size: ' + name);
    }
    const v = parseInt(vStr);
    assert(v % 8 === 0 && v >= 8 && v <= 256);
    return v / 8;
  }
  if (name.startsWith('int')) {
    const vStr = name.substring(3) || '256';
    const re = /^[1-9]\d*$/;
    if (!re.test(vStr)) {
      throw new Error('ERROR: Invalid uint size: ' + name);
    }
    const v = parseInt(vStr);
    assert(v % 8 === 0 && v >= 8 && v <= 256);
    return v / 8;
  }
  if (name === 'address') {
    return 20;
  }
  if (name.startsWith('bytes')) {
    const vStr = name.substring(5) || '32';
    const re = /^[1-9]\d+$/;
    if (!re.test(vStr)) {
      throw new Error('ERROR: Invalid elementary type: ' + name);
    }
    const v = parseInt(vStr);
    assert(v >= 1 && v <= 32);
    return v;
  }
  if (name === 'bool') {
    return 1;
  }
  return 0;
}

export function varDeclToBytes(varDecl: VariableDeclaration, userTypeDefinitions: UserTypeDefinition[]): number {
  const typeName = varDecl.typeName!;
  if (['Mapping', 'ArrayTypeName'].includes(typeName.type)) {
    return 32;
  }
  if (typeName.type === 'UserDefinedTypeName') {
    const structName = (typeName as UserDefinedTypeName).namePath;
    for (const astStructDefinition of userTypeDefinitions) {
      if (astStructDefinition.name === structName) {
        return userTypeDefinitionToBytes(astStructDefinition, userTypeDefinitions);
      }
    }
  }
  const name = (typeName as ElementaryTypeName).name;

  if (name === 'string' || name === 'bytes') {
    return 32;
  }

  return elementaryTypeNameToByte(name);
}
