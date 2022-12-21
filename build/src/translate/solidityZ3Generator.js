import { VarTypeKind } from '../sol_parsing/vartype.js';
import { elementaryTypeNameToByte } from '../sol_parsing/var_parsing.js';
import assert from 'assert';
export const makeZ3GlobalStorage = (z3, tags = '') => {
    return z3.Array.const('global_storage' + tags, z3.BitVec.sort(160), z3.Array.sort(z3.BitVec.sort(256), z3.BitVec.sort(256)));
};
export const makeZ3Balances = (z3, tags = '') => {
    return z3.Array.const('balances' + tags, z3.BitVec.sort(160), z3.BitVec.sort(256));
};
export function isAnnotatedZ3(expr) {
    return expr !== undefined && expr !== null && expr['solidityType'] !== undefined;
}
export function isAnnotatedZ3Expr(expr) {
    return isAnnotatedZ3(expr) && expr['expr'] !== undefined;
}
export function isAnnotatedZ3Mapping(expr) {
    return isAnnotatedZ3(expr) && expr['indexSort'] !== undefined;
}
function solidityElementaryVarToUnslottedZ3Generator(type, contractName) {
    return (z3, globalStorage) => {
        return (slot, offset) => {
            const Z3_contract_addr = z3.BitVec.const(contractName + '_addr', 160);
            let data = globalStorage.select(Z3_contract_addr).select(slot);
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
function solidityMappingVarToUnslottedZ3Generator(type, contractName) {
    const keyType = type.keyType;
    const valueType = type.valueType;
    if (keyType.type !== VarTypeKind.ElementaryTypeName) {
        throw new Error('Unsupported: Mapping key type must be elementary');
    }
    assert(keyType.name !== 'string ' && keyType.name !== 'bytes');
    const inputBytes = elementaryTypeNameToByte(keyType.name);
    assert(inputBytes <= 32);
    const subcallUnslottedGenerator = solidityVarToUnslottedZ3Generator(valueType, contractName);
    return (z3, global_storage) => {
        const keccak = z3.Function.declare('keccak256_512', z3.BitVec.sort(512), z3.BitVec.sort(256));
        const indexSort = keyType.name === 'boolean' ? z3.Bool.sort() : z3.BitVec.sort(inputBytes * 8);
        return (slot, offset) => {
            assert(offset === undefined);
            const getFunction = (idx) => {
                assert(idx.sort.eqIdentity(indexSort));
                if (idx.sort.eqIdentity(z3.Bool.sort())) {
                    idx = z3.If(idx, z3.BitVec.val(1, 8), z3.BitVec.val(0, 8));
                }
                assert(z3.isBitVec(idx));
                const slotHalf0 = inputBytes == 32 ? idx : z3.Concat(z3.BitVec.val(0, 256 - inputBytes * 8), idx);
                const hash_input = z3.Concat(slotHalf0, slot);
                const hash_val = keccak.call(hash_input);
                return subcallUnslottedGenerator(z3, global_storage)(hash_val, undefined);
            };
            return {
                solidityType: type,
                indexSort,
                get: getFunction,
            };
        };
    };
}
function solidityVarToUnslottedZ3Generator(type, contractName) {
    switch (type.type) {
        case VarTypeKind.ElementaryTypeName:
            return solidityElementaryVarToUnslottedZ3Generator(type, contractName);
        case VarTypeKind.Mapping:
            return solidityMappingVarToUnslottedZ3Generator(type, contractName);
        default:
            throw new Error('Unsupported: Var type ' + VarTypeKind[type.type] + ':\n' + JSON.stringify(type, null, 2));
    }
}
function getGlobalVarZ3Generator(solidityData, contract) {
    const globalZ3Vars = new Map();
    const contractId = solidityData.contractId[contract];
    const contractData = solidityData.typeObjects[contractId];
    const contractVarData = contractData.vars;
    for (const [varName, contractVar] of Object.entries(contractVarData)) {
        try {
            const unslottedGenerator = solidityVarToUnslottedZ3Generator(contractVar.type, contract);
            assert(contractVar.slot !== undefined);
            if (contractVar.slot.slot[0] !== contractVar.slot.slot[1]) {
                throw new Error('Unsupported: Global vars must be in a single slot');
            }
            const generator = (z3, global_storage) => {
                const slot = z3.BitVec.val(contractVar.slot.slot[0], 256);
                return unslottedGenerator(z3, global_storage)(slot, contractVar.slot.intraSlot?.[0]);
            };
            globalZ3Vars.set(contractVar.name, generator);
        }
        catch (e) {
            console.log('WARNING: ' + e.message);
            console.log('WARNING: Skipping global var: ' + contractVar.name);
        }
    }
    return globalZ3Vars;
}
export function solidityDataToZ3Generators(solidityData, contract) {
    const globalVarZ3Generators = getGlobalVarZ3Generator(solidityData, contract);
    return {
        solidityData,
        globalVarZ3Generators,
    };
}
