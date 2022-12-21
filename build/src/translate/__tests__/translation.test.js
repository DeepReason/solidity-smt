import { textToZ3 } from "../toZ3.js";
import { getSolidityData } from '../../sol_parsing/parse_solidity.js';
import makeZ3 from '../../z3/z3.js';
import { makeZ3GlobalStorage, solidityDataToZ3Generators, } from "../solidityZ3Generator.js";
import fs from "fs";
import path from "path";
import solc from "solc";
describe('Test add func valid', () => {
    let z3;
    let z3SolidityGenerators;
    let Z3_STORAGE;
    let Z3_STORAGE_BEFORE;
    let Z3_X;
    let Z3_Y;
    let Z3_Z;
    let Z3_BALANCES;
    jest.setTimeout(10000);
    beforeAll(async () => {
        z3 = await makeZ3();
        // Read from the file examples/VaultBasic.sol
        const code = fs.readFileSync(path.join(__dirname, 'examples/VaultBasic.sol'), 'utf8');
        const solc_output = JSON.parse(solc.compile(JSON.stringify({
            "language": "Solidity",
            "sources": {
                "VaultBasic.sol": {
                    "content": code
                },
            },
            "settings": {
                "optimizer": {
                    "enabled": false,
                    "runs": 200
                },
                "outputSelection": {
                    "*": {
                        "*": [
                            "abi",
                            "evm.bytecode",
                            "evm.deployedBytecode",
                            "evm.methodIdentifiers",
                            "metadata"
                        ],
                        "": [
                            "ast"
                        ]
                    }
                }
            }
        })));
        const solidityData = getSolidityData(solc_output);
        z3SolidityGenerators = solidityDataToZ3Generators(solidityData, 'VaultBasic');
        const Z3_ADDR = z3.BitVec.const('VaultBasic_addr', 160);
        Z3_STORAGE = makeZ3GlobalStorage(z3).select(Z3_ADDR);
        Z3_STORAGE_BEFORE = makeZ3GlobalStorage(z3, '@before').select(Z3_ADDR);
        const Z3_SLOT_0 = (storage) => storage.select(z3.BitVec.val(0, 256));
        const Z3_SLOT_1 = (storage) => storage.select(z3.BitVec.val(1, 256));
        // const Z3_SLOT_2 = (storage: StorageSort) => storage.select(z3.BitVec.val(2, 256)) as BitVec<256>;
        const keccak512 = z3.Function.declare('keccak256_512', z3.BitVec.sort(512), z3.BitVec.sort(256));
        Z3_X = (storage) => Z3_SLOT_0(storage);
        Z3_Y = (storage) => z3.Extract(255, 192, Z3_SLOT_1(storage));
        Z3_Z = (storage) => z3.Extract(191, 32, Z3_SLOT_1(storage));
        Z3_BALANCES = (storage, idx) => storage.select(keccak512.call(z3.Concat(z3.BitVec.val(0, 96), idx, z3.BitVec.val(2, 256))));
    });
    it('Arithmetic Expression', async () => {
        const expr = 'x';
        const result = textToZ3(expr, z3, z3SolidityGenerators);
        const expected = Z3_X(Z3_STORAGE);
        expect(result.eqIdentity(expected)).toBeTruthy();
    });
    it('Addition Expression', async () => {
        const expr = 'x + x';
        const result = textToZ3(expr, z3, z3SolidityGenerators);
        const expected = Z3_X(Z3_STORAGE).add(Z3_X(Z3_STORAGE));
        expect(result.eqIdentity(expected)).toBeTruthy();
    });
    it('BitVector Casting', async () => {
        const expr = 'x + uint256(y)';
        const result = textToZ3(expr, z3, z3SolidityGenerators);
        const expected = Z3_X(Z3_STORAGE).add(z3.Concat(z3.BitVec.val(0, 192), Z3_Y(Z3_STORAGE)));
        expect(result.eqIdentity(expected)).toBeTruthy();
    });
    it('BitVector Implicit Type Conversion', async () => {
        const expr = 'x + y';
        const result = textToZ3(expr, z3, z3SolidityGenerators);
        const expected = Z3_X(Z3_STORAGE).add(z3.Concat(z3.BitVec.val(0, 192), Z3_Y(Z3_STORAGE)));
        expect(result.eqIdentity(expected)).toBeTruthy();
    });
    it('BitVector and Number Addition', async () => {
        const expr = 'x + 2';
        const result = textToZ3(expr, z3, z3SolidityGenerators);
        const expected = Z3_X(Z3_STORAGE).add(z3.BitVec.val(2, 256));
        expect(result.eqIdentity(expected)).toBeTruthy();
    });
    it('Balances', async () => {
        const expr = 'balance[z]';
        const result = textToZ3(expr, z3, z3SolidityGenerators);
        const expected = Z3_BALANCES(Z3_STORAGE, Z3_Z(Z3_STORAGE));
        expect(result.eqIdentity(expected)).toBeTruthy();
    });
    it('Message sender', async () => {
        const expr = 'msg.sender';
        const result = textToZ3(expr, z3, z3SolidityGenerators);
        const expected = z3.BitVec.const('sender', 160);
        expect(result.eqIdentity(expected)).toBeTruthy();
    });
    it('Tags', async () => {
        const expr = 'x@before';
        const result = textToZ3(expr, z3, z3SolidityGenerators);
        const expected = Z3_X(Z3_STORAGE_BEFORE);
        expect(result.eqIdentity(expected)).toBeTruthy();
    });
});
