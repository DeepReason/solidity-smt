import { textToZ3 } from "../toZ3";
import { getSolidityData } from '../../sol_parsing/parse_solidity';
import { BitVec, BitVecSort, SMTArray } from 'z3-solver';
import makeZ3, { Z3Obj } from '../../z3/z3';
import {
  makeZ3GlobalStorage,
  solidityDataToZ3Generators,
  Z3SolidityGenerators,
} from "../solidityZ3Generator";
import fs from "fs";
import path from "path";
import solc from "solc";
type StorageSort = SMTArray<'main', [BitVecSort<256, 'main'>], BitVecSort<256, 'main'>>;

describe('Test add func valid', () => {
  let z3: Z3Obj;
  let z3SolidityGenerators: Z3SolidityGenerators;
  let Z3_STORAGE: StorageSort;
  let Z3_STORAGE_BEFORE: StorageSort;

  let Z3_X: (base_arr: StorageSort) => BitVec<256>;
  let Z3_Y: (base_arr: StorageSort) => BitVec<64>;
  let Z3_Z: (base_arr: StorageSort) => BitVec<160>;
  let Z3_BALANCES: (base_arr: StorageSort, idx: BitVec<160>) => BitVec;

  jest.setTimeout(10000);

  beforeAll(async () => {
    z3 = await makeZ3();

    // Read from the file examples/VaultBasic.sol
    const code = fs.readFileSync(path.join(__dirname, 'examples/VaultBasic.sol'), 'utf8');
    const solc_output = JSON.parse(solc.compile(JSON.stringify(
      {
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
      }
    )));

    const solidityData = getSolidityData(solc_output);

    z3SolidityGenerators = solidityDataToZ3Generators(solidityData, 'VaultBasic');

    const Z3_ADDR = z3.BitVec.const('VaultBasic_addr', 160);
    Z3_STORAGE = makeZ3GlobalStorage(z3).select(Z3_ADDR) as StorageSort;
    Z3_STORAGE_BEFORE = makeZ3GlobalStorage(z3, '@before').select(Z3_ADDR) as StorageSort;

    const Z3_SLOT_0 = (storage: StorageSort) => storage.select(z3.BitVec.val(0, 256)) as BitVec<256>;
    const Z3_SLOT_1 = (storage: StorageSort) => storage.select(z3.BitVec.val(1, 256)) as BitVec<256>;
    // const Z3_SLOT_2 = (storage: StorageSort) => storage.select(z3.BitVec.val(2, 256)) as BitVec<256>;

    const keccak512 = z3.Function.declare('keccak256_512', z3.BitVec.sort(512), z3.BitVec.sort(256));

    Z3_X = (storage: StorageSort) => Z3_SLOT_0(storage);
    Z3_Y = (storage: StorageSort) => z3.Extract(255, 192, Z3_SLOT_1(storage)) as BitVec<64>;
    Z3_Z = (storage: StorageSort) => z3.Extract(191, 32, Z3_SLOT_1(storage)) as BitVec<160>;
    Z3_BALANCES = (storage: StorageSort, idx: BitVec<160>) =>
      storage.select(
        keccak512.call(z3.Concat(z3.BitVec.val(0, 96), idx, z3.BitVec.val(2, 256)) as BitVec<512>),
      ) as BitVec;
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

    const expected = Z3_X(Z3_STORAGE).add(z3.Concat(z3.BitVec.val(0, 192), Z3_Y(Z3_STORAGE)) as BitVec<256>);
    expect(result.eqIdentity(expected)).toBeTruthy();
  });

  it('BitVector Implicit Type Conversion', async () => {
    const expr = 'x + y';

    const result = textToZ3(expr, z3, z3SolidityGenerators);

    const expected = Z3_X(Z3_STORAGE).add(z3.Concat(z3.BitVec.val(0, 192), Z3_Y(Z3_STORAGE)) as BitVec<256>);
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
