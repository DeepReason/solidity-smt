import assert from 'assert';
import {
  ElementaryTypeName,
  EnumDefinition,
  Mutability,
  StructDefinition,
  TypeName,
  UserDefinedTypeName,
  VariableDeclaration,
} from 'solc-typed-ast';

export function typeNameToString(typeName: TypeName): string {
  return typeName.typeString;
}

export type UserTypeDefinition = StructDefinition | EnumDefinition;

export function userTypeDefinitionToBytes(def: UserTypeDefinition): number {
  if (def.type === 'EnumDefinition') {
    const enumDefinition = def as EnumDefinition;
    const target = enumDefinition.vMembers.length;
    let res = 8;
    while (1 << res < target) {
      res += 8;
    }
    return res / 8;
  } else {
    const structDefinition = def as StructDefinition;
    let bytes = 0;
    for (const variableDecl of structDefinition.vMembers || []) {
      const newBytes = varDeclToBytes(variableDecl);
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

export function stateVarDeclToBytes(varDecl: VariableDeclaration): number {
  if (varDecl.mutability !== Mutability.Mutable) {
    return 0;
  }
  return varDeclToBytes(varDecl);
}

export function elementaryTypeNameToBytes(name: string): number {
  if (name.startsWith('uint')) {
    const vStr = name.substring(4) || '256';
    const re = /^[1-9]\d*$/;
    if (!re.test(vStr)) {
      throw new Error('Invalid uint size: ' + name);
    }
    const v = parseInt(vStr);
    assert(v % 8 === 0 && v >= 8 && v <= 256);
    return v / 8;
  }
  if (name.startsWith('int')) {
    const vStr = name.substring(3) || '256';
    const re = /^[1-9]\d*$/;
    if (!re.test(vStr)) {
      throw new Error('Invalid uint size: ' + name);
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
    const re = /^[1-9]\d*$/;
    if (!re.test(vStr)) {
      throw new Error('Invalid elementary type: ' + name);
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

export function varDeclToBytes(varDecl: VariableDeclaration): number {
  const vType = varDecl.vType!;
  if (['Mapping', 'ArrayTypeName'].includes(vType.type)) {
    return 32;
  }
  if (vType.type === 'UserDefinedTypeName') {
    const typeDef = (vType as UserDefinedTypeName).vReferencedDeclaration as UserTypeDefinition;
    return userTypeDefinitionToBytes(typeDef);
  }
  const name = (vType as ElementaryTypeName).name;

  if (name === 'string' || name === 'bytes') {
    return 32;
  }

  return elementaryTypeNameToBytes(name);
}
