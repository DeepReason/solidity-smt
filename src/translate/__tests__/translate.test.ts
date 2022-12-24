import { translateToZ3 } from '../translateToZ3';
import { BitVec, BitVecSort, SMTArray } from 'z3-solver';
import { makeZ3Balances, makeZ3GlobalStorage } from '../solidityZ3Generator';
import fs from 'fs';
import path from 'path';
import { ParsedSolidityData } from '../../sol_parsing';
import { dumps_expr, makeZ3, repr_of_expr, Z3Obj } from '../../z3';
import { ExposedImmutables } from '../exposedImmutables';
import assert from 'assert';

type StorageSort = SMTArray<'main', [BitVecSort<256, 'main'>], BitVecSort<256, 'main'>>;

describe('Test textToZ3', () => {
  let z3: Z3Obj;
  let parsedSolidity: ParsedSolidityData;
  let exposedImmutables: ExposedImmutables;

  let SENDER: BitVec<160>;

  let Z3_STORAGE: StorageSort;
  let Z3_STORAGE_BEFORE: StorageSort;
  let Z3_STORAGE_AFTER: StorageSort;

  let Z3_X: (base_arr: StorageSort) => BitVec<256>;
  let Z3_Y: (base_arr: StorageSort) => BitVec<64>;
  let Z3_Z: (base_arr: StorageSort) => BitVec<160>;
  let Z3_BALANCES: (base_arr: StorageSort, idx: BitVec<160>) => BitVec;

  jest.setTimeout(10000);

  beforeAll(async () => {
    z3 = await makeZ3();

    parsedSolidity = JSON.parse(fs.readFileSync(path.join(__dirname, 'examples/parsed_solidity.json'), 'utf8'));
    exposedImmutables = JSON.parse(fs.readFileSync(path.join(__dirname, 'examples/exposed_immutables.json'), 'utf8'));

    const Z3_ADDR = z3.BitVec.const('VaultBasic_addr', 160);

    SENDER = z3.BitVec.const('sender', 160);

    Z3_STORAGE = makeZ3GlobalStorage(z3, '').select(Z3_ADDR) as StorageSort;
    Z3_STORAGE_BEFORE = makeZ3GlobalStorage(z3, '@before').select(Z3_ADDR) as StorageSort;
    Z3_STORAGE_AFTER = makeZ3GlobalStorage(z3, '@after').select(Z3_ADDR) as StorageSort;

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

  async function unerroredTranslation(input: string, contractName: string) {
    const result = await translateToZ3(input, contractName, parsedSolidity, exposedImmutables);
    expect(result).not.toHaveProperty('error');
    assert(!('error' in result));
    return result;
  }

  async function erroredTranslation(input: string, contractName: string) {
    const result = await translateToZ3(input, contractName, parsedSolidity, exposedImmutables);
    expect(result).toHaveProperty('error');
    assert('error' in result);
    return result;
  }

  it('Arithmetic Expression', async () => {
    const input = 'x';
    const { expr, warnings } = await unerroredTranslation(input, 'VaultBasic');

    const expected = Z3_X(Z3_STORAGE);
    expect(expr.eqIdentity(expected)).toBeTruthy();
  });

  it('Addition Expression', async () => {
    const input = 'x + x';
    const { expr, warnings } = await unerroredTranslation(input, 'VaultBasic');

    const expected = Z3_X(Z3_STORAGE).add(Z3_X(Z3_STORAGE));
    expect(expr.eqIdentity(expected)).toBeTruthy();
  });

  it('BitVector Casting', async () => {
    const input = 'x + uint256(y)';
    const { expr, warnings } = await unerroredTranslation(input, 'VaultBasic');

    const expected = Z3_X(Z3_STORAGE).add(z3.Concat(z3.BitVec.val(0, 192), Z3_Y(Z3_STORAGE)) as BitVec<256>);
    expect(expr.eqIdentity(expected)).toBeTruthy();
  });

  it('BitVector Implicit Type Conversion', async () => {
    const input = 'x + y';
    const { expr, warnings } = await unerroredTranslation(input, 'VaultBasic');

    const expected = Z3_X(Z3_STORAGE).add(z3.Concat(z3.BitVec.val(0, 192), Z3_Y(Z3_STORAGE)) as BitVec<256>);
    expect(expr.eqIdentity(expected)).toBeTruthy();
  });

  it('BitVector and Number Addition', async () => {
    const input = 'x + 2';
    const { expr, warnings } = await unerroredTranslation(input, 'VaultBasic');

    const expected = Z3_X(Z3_STORAGE).add(z3.BitVec.val(2, 256));
    expect(expr.eqIdentity(expected)).toBeTruthy();
  });

  it('Balances', async () => {
    const input = 'balance[z]';
    const { expr, warnings } = await unerroredTranslation(input, 'VaultBasic');

    const expected = Z3_BALANCES(Z3_STORAGE, Z3_Z(Z3_STORAGE));

    expect(expr.eqIdentity(expected)).toBeTruthy();
  });

  it('Message sender', async () => {
    const input = 'msg.sender';
    const { expr, warnings } = await unerroredTranslation(input, 'VaultBasic');

    const expected = SENDER;
    expect(expr.eqIdentity(expected)).toBeTruthy();
  });

  it('Tags', async () => {
    const input = 'x@before';
    const { expr, warnings } = await unerroredTranslation(input, 'VaultBasic');

    const expected = Z3_X(Z3_STORAGE_BEFORE);
    expect(expr.eqIdentity(expected)).toBeTruthy();
  });

  it('Quantifier', async () => {
    const input = 'ForAll([address a], a.balance <= 200)';
    const { expr, warnings } = await unerroredTranslation(input, 'VaultBasic');
    expect(
      expr.eqIdentity(
        z3.ForAll(
          [z3.BitVec.const('a', 160)],
          z3.ULE(makeZ3Balances(z3, '').select(z3.BitVec.const('a', 160)), z3.BitVec.val(200, 256)),
        ),
      ),
    ).toBeTruthy();
  });

  it('Arithmetic Expression', async () => {
    const input = 'x + 7';
    const { expr, warnings } = await unerroredTranslation(input, 'VaultBasic');
    expect(expr.eqIdentity(Z3_X(Z3_STORAGE).add(z3.BitVec.val(7, 256)) as BitVec<256>)).toBeTruthy();
  });

  it('Accessing Immutable', async () => {
    const input = 't == 5';
    const { expr, warnings } = await unerroredTranslation(input, 'VaultBasic');
    expect(expr.eqIdentity(z3.BitVec.val(5, 256).eq(z3.BitVec.val(5, 256)))).toBeTruthy();
  });

  it('Tagging intermediate', async () => {
    const input = 'balance@after[msg.sender] > 0';
    const { expr, warnings } = await unerroredTranslation(input, 'VaultBasic');
    expect(expr.eqIdentity(Z3_BALANCES(Z3_STORAGE_AFTER, SENDER).ugt(z3.BitVec.val(0, 256)))).toBeTruthy();
  });

  describe('Testing Errors', () => {
    it('Empty Text', async () => {
      const result = await erroredTranslation('', 'VaultBasic');
      expect(result.error).toBe('Error: Unexpected token <EOF>');
    });

    it('Unknown identifier', async () => {
      const result = await erroredTranslation('blah', 'Spec');
      expect(result.error).toBe('Error: Unknown identifier: blah');
    });

    it('Non-expression', async () => {
      const result = await erroredTranslation('test', 'VaultBasic');
      expect(result.error).toBe('Error: Expression is a mapping');
    });
  });
});
