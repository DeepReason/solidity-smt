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
  Z3LowLevel,
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

// Run if main (testing)
if (require.main === module) {
  (async () => {
    const z3 = await makeZ3();
    const x = z3.BitVec.const('x', 256);
    const y = z3.BitVec.const('y', 256);
    const z = z3.BitVec.const('z', 256);
    const xPlusY = x.add(y);
    const xPlusZ = x.add(z);
    const xPlusYEMulPlusZ = xPlusY.mul(xPlusZ);

    const str = dumps_expr(xPlusYEMulPlusZ);
    console.log(str);

    const expr = loads_expr(z3, str) as Expr;
    console.log(expr.sexpr());

    const to_check = expr.eq(z3.Const('test', expr.sort));

    const solver = new z3.Solver();
    solver.add(to_check);
    const cr = await solver.check();
    console.log(cr);
    assert(cr === 'sat');

    const model = solver.model();
    let modelStr = model.sexpr();
    modelStr = modelStr.replace(/\n/g, ' ');
    console.log("Model: ", modelStr);

    const newSolver = new z3.Solver();
    newSolver.fromString(modelStr);
    newSolver.add(z3.Bool.val(true));
    const newCr = await newSolver.check();
    console.log(newCr);
    console.log(newSolver.model().sexpr());
  })();
}

export default makeZ3;