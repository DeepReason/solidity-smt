import {
  init,
  Z3_decl_kind,
  Z3_sort_kind,
  Arith,
  CoercibleToArith,
  BitVec,
  BitVecNum,
  Sort,
  FuncDecl,
  IntNum,
  Quantifier,
  BitVecSort,
  SMTArray,
  SMTArraySort,
  Bool,
  Expr, ContextCtor, Context,
} from 'z3-solver';
import { dumps_expr, loads_expr } from './dumps_loads';
import assert from 'assert';

let ctx: undefined | ContextCtor;
let Z3C: any;

async function getContext(): Promise<ContextCtor> {
  if (ctx === undefined) {
    const {
      Z3,
      Context,
    } = await init();
    ctx = Context;
    Z3C = Z3;
  }
  return ctx;
}

export type Z3Obj = Context<'main'>;

let z3Mem: Z3Obj;

async function makeZ3(): Promise<Z3Obj> {
  if (z3Mem === undefined) z3Mem = (await getContext())('main');
  return z3Mem;
}

export type { Arith, Expr, Bool, BitVec, BitVecNum, Sort, FuncDecl, IntNum, Quantifier, BitVecSort, SMTArray, SMTArraySort, CoercibleToArith };
export { Z3_decl_kind, Z3_sort_kind };

export default makeZ3;