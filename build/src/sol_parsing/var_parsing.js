import assert from 'assert';
import { Mutability, } from 'solc-typed-ast';
export function typeNameToString(typeName) {
    return typeName.typeString;
}
function userTypeDefinitionToBytes(def) {
    if (def.type === 'EnumDefinition') {
        const enumDefinition = def;
        const target = enumDefinition.vMembers.length;
        let res = 8;
        while (1 << res < target) {
            res += 8;
        }
        return res / 8;
    }
    else {
        const structDefinition = def;
        let bytes = 0;
        for (const variableDecl of structDefinition.vMembers) {
            const newBytes = varDeclToBytes(variableDecl);
            const nextSlot = bytes % 32 === 0 ? bytes : (bytes & ~0x1f) + 32;
            if (bytes + newBytes <= nextSlot) {
                bytes += newBytes;
            }
            else {
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
export function stateVarDeclToBytes(varDecl) {
    if (varDecl.mutability === Mutability.Immutable) {
        return 0;
    }
    return varDeclToBytes(varDecl);
}
export function elementaryTypeNameToByte(name) {
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
export function varDeclToBytes(varDecl) {
    const vType = varDecl.vType;
    if (['Mapping', 'ArrayTypeName'].includes(vType.type)) {
        return 32;
    }
    if (vType.type === 'UserDefinedTypeName') {
        const typeDef = vType.vReferencedDeclaration;
        return userTypeDefinitionToBytes(typeDef);
    }
    const name = vType.name;
    if (name === 'string' || name === 'bytes') {
        return 32;
    }
    return elementaryTypeNameToByte(name);
}
