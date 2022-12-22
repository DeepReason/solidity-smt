import { translateToZ3 } from '../translateToZ3';
import { BitVec, BitVecSort, SMTArray } from 'z3-solver';
import { makeZ3Balances, makeZ3GlobalStorage } from '../solidityZ3Generator';
import fs from 'fs';
import path from 'path';
import { ParsedSolidityData } from '../../sol_parsing';
import { dumps_expr, makeZ3, Z3Obj } from '../../z3';
import { ExposedImmutables } from '../exposedImmutables';

type StorageSort = SMTArray<'main', [BitVecSort<256, 'main'>], BitVecSort<256, 'main'>>;

describe('Test textToZ3', () => {
  let z3: Z3Obj;
  let parsedSolidity: ParsedSolidityData;
  let exposedImmutables: ExposedImmutables;

  let Z3_STORAGE: StorageSort;
  let Z3_STORAGE_BEFORE: StorageSort;

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
    Z3_STORAGE = makeZ3GlobalStorage(z3, '').select(Z3_ADDR) as StorageSort;
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
    const { expr: result, warnings } = await translateToZ3(expr, 'VaultBasic', parsedSolidity, exposedImmutables);

    const expected = Z3_X(Z3_STORAGE);
    expect(result.eqIdentity(expected)).toBeTruthy();
  });

  it('Addition Expression', async () => {
    const expr = 'x + x';
    const { expr: result, warnings } = await translateToZ3(expr, 'VaultBasic', parsedSolidity, exposedImmutables);

    const expected = Z3_X(Z3_STORAGE).add(Z3_X(Z3_STORAGE));
    expect(result.eqIdentity(expected)).toBeTruthy();
  });

  it('BitVector Casting', async () => {
    const expr = 'x + uint256(y)';
    const { expr: result, warnings } = await translateToZ3(expr, 'VaultBasic', parsedSolidity, exposedImmutables);

    const expected = Z3_X(Z3_STORAGE).add(z3.Concat(z3.BitVec.val(0, 192), Z3_Y(Z3_STORAGE)) as BitVec<256>);
    expect(result.eqIdentity(expected)).toBeTruthy();
  });

  it('BitVector Implicit Type Conversion', async () => {
    const expr = 'x + y';
    const { expr: result, warnings } = await translateToZ3(expr, 'VaultBasic', parsedSolidity, exposedImmutables);

    const expected = Z3_X(Z3_STORAGE).add(z3.Concat(z3.BitVec.val(0, 192), Z3_Y(Z3_STORAGE)) as BitVec<256>);
    expect(result.eqIdentity(expected)).toBeTruthy();
  });

  it('BitVector and Number Addition', async () => {
    const expr = 'x + 2';
    const { expr: result, warnings } = await translateToZ3(expr, 'VaultBasic', parsedSolidity, exposedImmutables);

    const expected = Z3_X(Z3_STORAGE).add(z3.BitVec.val(2, 256));
    expect(result.eqIdentity(expected)).toBeTruthy();
  });

  it('Balances', async () => {
    const expr = 'balance[z]';
    const { expr: result, warnings } = await translateToZ3(expr, 'VaultBasic', parsedSolidity, exposedImmutables);

    const expected = Z3_BALANCES(Z3_STORAGE, Z3_Z(Z3_STORAGE));

    expect(result.eqIdentity(expected)).toBeTruthy();
  });

  it('Message sender', async () => {
    const expr = 'msg.sender';
    const { expr: result, warnings } = await translateToZ3(expr, 'VaultBasic', parsedSolidity, exposedImmutables);

    const expected = z3.BitVec.const('sender', 160);
    expect(result.eqIdentity(expected)).toBeTruthy();
  });

  it('Tags', async () => {
    const expr = 'x@before';
    const { expr: result, warnings } = await translateToZ3(expr, 'VaultBasic', parsedSolidity, exposedImmutables);

    const expected = Z3_X(Z3_STORAGE_BEFORE);
    expect(result.eqIdentity(expected)).toBeTruthy();
  });

  it('Quantifier', async () => {
    const expr = 'ForAll([address a], a.balance <= 200)';
    const { expr: result, warnings } = await translateToZ3(expr, 'VaultBasic', parsedSolidity, exposedImmutables);
    expect(
      result.eqIdentity(
        z3.ForAll(
          [z3.BitVec.const('a', 160)],
          z3.ULE(makeZ3Balances(z3, '').select(z3.BitVec.const('a', 160)), z3.BitVec.val(200, 256)),
        ),
      ),
    ).toBeTruthy();
  });

  it('Invalid Text', async () => {
    const result = await translateToZ3('', 'VaultBasic', parsedSolidity, exposedImmutables);
    expect(result.error).toBe('Unexpected token <EOF>');
  });

  it('Arithmetic Expression', async () => {
    const result = await translateToZ3('x + 7', 'VaultBasic', parsedSolidity, exposedImmutables);
    expect(dumps_expr(result.expr)).toEqual(
      '(declare-fun __deepreason_claim_tmp () (_ BitVec 256)) (declare-fun VaultBasic_addr () (_ BitVec 160)) (declare-fun global_storage              ()              (Array (_ BitVec 160) (Array (_ BitVec 256) (_ BitVec 256)))) (assert (= (bvadd (select (select global_storage VaultBasic_addr)                   #x0000000000000000000000000000000000000000000000000000000000000000)           #x0000000000000000000000000000000000000000000000000000000000000007)    __deepreason_claim_tmp)) ',
    );
  });
});
