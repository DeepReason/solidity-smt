import { repr_of_expr } from '../repr';
import makeZ3, { Z3Obj } from '../z3';

describe('Representation Testing', () => {
  let z3: Z3Obj;

  beforeAll(async () => {
    z3 = await makeZ3();
  });

  it('should be able to represent a number', () => {
    expect(repr_of_expr(0)).toEqual('0');
  });

  it('should be able to represent a number', () => {
    expect(repr_of_expr(z3.BitVec.val(1, 256).add(
      z3.BitVec.val(2, 256)
    ))).toEqual('1 + 2');
  });

  it('should be able to represent a quantifier', () => {
    const quantifier = z3.ForAll(
      [z3.BitVec.const('a', 256)],
      z3.BitVec.const('a', 256).eq(z3.BitVec.val(1, 256))
    )
    expect(repr_of_expr(quantifier)).toEqual(
      'ForAll(\n  [a],\n  a == 1\n)'
    );
  });

  it('represents large numbers as hex', () => {
    expect(repr_of_expr(z3.BitVec.val(2 ** 40, 160))).toEqual('bv160(0x10000000000)');
    expect(repr_of_expr(z3.BitVec.val(-(2 ** 40), 160))).toEqual('bv160(-0x10000000000)');
  })

});