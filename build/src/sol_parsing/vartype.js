import assert from 'assert';
import { elementaryTypeNameToByte } from './var_parsing.js';
export var VarTypeKind;
(function (VarTypeKind) {
    VarTypeKind[VarTypeKind["Mapping"] = 0] = "Mapping";
    VarTypeKind[VarTypeKind["ArrayTypeName"] = 1] = "ArrayTypeName";
    VarTypeKind[VarTypeKind["ElementaryTypeName"] = 2] = "ElementaryTypeName";
    VarTypeKind[VarTypeKind["UserDefinedTypeName"] = 3] = "UserDefinedTypeName";
})(VarTypeKind || (VarTypeKind = {}));
export function makeElementaryVarType(name) {
    return {
        type: VarTypeKind.ElementaryTypeName,
        name,
        stateMutability: null,
    };
}
export function varTypeToString(varType) {
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
export function isSameType(varType1, varType2) {
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
            }
            else if (name1.startsWith('int') && name2.startsWith('int')) {
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
export function typeNameToVarType(typeName) {
    if (typeName.type === 'Mapping') {
        const mappingTypeNames = typeName;
        return {
            type: VarTypeKind.Mapping,
            keyType: typeNameToVarType(mappingTypeNames.vKeyType),
            valueType: typeNameToVarType(mappingTypeNames.vValueType),
        };
    }
    if (typeName.type === 'ArrayTypeName') {
        const arrayTypeName = typeName;
        return {
            type: VarTypeKind.ArrayTypeName,
            baseType: typeNameToVarType(arrayTypeName.vBaseType),
            length: arrayTypeName.vLength,
        };
    }
    if (typeName.type === 'ElementaryTypeName') {
        const elementaryTypeName = typeName;
        return {
            type: VarTypeKind.ElementaryTypeName,
            name: elementaryTypeName.name,
            stateMutability: elementaryTypeName.stateMutability,
        };
    }
    if (typeName.type === 'UserDefinedTypeName') {
        const userDefinedTypeName = typeName;
        return {
            type: VarTypeKind.UserDefinedTypeName,
            name: userDefinedTypeName.path.name,
        };
    }
    throw new Error('Unknown type: ' + typeName.type);
}
