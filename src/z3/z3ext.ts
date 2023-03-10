import { SMTArray, Z3_decl_kind, Z3Obj } from './z3';
import { BitVecSort, CoercibleToArith, CoercibleToBitVec, Expr, Sort } from 'z3-solver';

const COMPARISON_OP_TO_FUNC = new Map<Z3_decl_kind, any>([
  [Z3_decl_kind.Z3_OP_LT, (z3: Z3Obj) => z3.LT],
  [Z3_decl_kind.Z3_OP_GT, (z3: Z3Obj) => z3.GT],
  [Z3_decl_kind.Z3_OP_GE, (z3: Z3Obj) => z3.GE],
  [Z3_decl_kind.Z3_OP_LE, (z3: Z3Obj) => z3.LE],
  [Z3_decl_kind.Z3_OP_ULT, (z3: Z3Obj) => z3.ULT],
  [Z3_decl_kind.Z3_OP_UGT, (z3: Z3Obj) => z3.UGT],
  [Z3_decl_kind.Z3_OP_UGEQ, (z3: Z3Obj) => z3.UGE],
  [Z3_decl_kind.Z3_OP_ULEQ, (z3: Z3Obj) => z3.ULE],
  [Z3_decl_kind.Z3_OP_SLT, (z3: Z3Obj) => z3.SLT],
  [Z3_decl_kind.Z3_OP_SGT, (z3: Z3Obj) => z3.SGT],
  [Z3_decl_kind.Z3_OP_SGEQ, (z3: Z3Obj) => z3.SGE],
  [Z3_decl_kind.Z3_OP_SLEQ, (z3: Z3Obj) => z3.SLE],
  [Z3_decl_kind.Z3_OP_EQ, (z3: Z3Obj) => z3.Eq],
  [Z3_decl_kind.Z3_OP_DISTINCT, (z3: Z3Obj) => z3.Distinct],
]);

const LOGIC_OP_TO_FUNC = new Map<Z3_decl_kind, any>([
  [Z3_decl_kind.Z3_OP_TRUE, (z3: Z3Obj) => z3.Bool.val(true)],
  [Z3_decl_kind.Z3_OP_FALSE, (z3: Z3Obj) => z3.Bool.val(false)],
  [Z3_decl_kind.Z3_OP_ITE, (z3: Z3Obj) => z3.If],
  [Z3_decl_kind.Z3_OP_AND, (z3: Z3Obj) => z3.And],
  [Z3_decl_kind.Z3_OP_OR, (z3: Z3Obj) => z3.Or],
  [Z3_decl_kind.Z3_OP_IFF, (z3: Z3Obj) => z3.Iff],
  [Z3_decl_kind.Z3_OP_XOR, (z3: Z3Obj) => z3.Xor],
  [Z3_decl_kind.Z3_OP_NOT, (z3: Z3Obj) => z3.Not],
  [Z3_decl_kind.Z3_OP_IMPLIES, (z3: Z3Obj) => z3.Implies],
]);

const MATH_OP_TO_FUNC = new Map<Z3_decl_kind, any>([
  [Z3_decl_kind.Z3_OP_ADD, (z3: Z3Obj) => z3.Add],
  [Z3_decl_kind.Z3_OP_SUB, (z3: Z3Obj) => z3.Sub],
  [Z3_decl_kind.Z3_OP_MUL, (z3: Z3Obj) => z3.Mul],
  [Z3_decl_kind.Z3_OP_DIV, (z3: Z3Obj) => z3.Div],
  [Z3_decl_kind.Z3_OP_IDIV, (z3: Z3Obj) => z3.Div],
  [Z3_decl_kind.Z3_OP_MOD, (z3: Z3Obj) => z3.Mod],
  [Z3_decl_kind.Z3_OP_BNEG, (z3: Z3Obj) => z3.Neg],
  [Z3_decl_kind.Z3_OP_BADD, (z3: Z3Obj) => z3.Add],
  [Z3_decl_kind.Z3_OP_BSUB, (z3: Z3Obj) => z3.Sub],
  [Z3_decl_kind.Z3_OP_BMUL, (z3: Z3Obj) => z3.Mul],
  [Z3_decl_kind.Z3_OP_BSDIV, (z3: Z3Obj) => z3.Div],
  [Z3_decl_kind.Z3_OP_BUDIV, (z3: Z3Obj) => z3.BUDiv],
  [Z3_decl_kind.Z3_OP_BSMOD, (z3: Z3Obj) => z3.Mod],
]);

const ARRAY_OP_TO_FUNC = new Map<Z3_decl_kind, any>([
  [Z3_decl_kind.Z3_OP_STORE, (z3: Z3Obj) => z3.Store],
  [Z3_decl_kind.Z3_OP_SELECT, (z3: Z3Obj) => z3.Select],
]);

const DECL_OP_TO_FUNC = new Map<Z3_decl_kind, any>([
  [Z3_decl_kind.Z3_OP_UNINTERPRETED, (z3: Z3Obj) => z3.Const],
  [Z3_decl_kind.Z3_OP_BNUM, (z3: Z3Obj) => (
    (x: number | bigint | boolean, bits: number | string | BitVecSort) => z3.BitVec.val(
      x, (typeof bits === 'string') ? Number(bits) : bits,
    )
  )],
  [Z3_decl_kind.Z3_OP_ANUM, (z3: Z3Obj) => z3.Int.val],
  [Z3_decl_kind.Z3_OP_CONCAT, (z3: Z3Obj) => z3.Concat],
]);

const PARAMETER_FUNC = new Map<Z3_decl_kind, any>([
  [Z3_decl_kind.Z3_OP_CONST_ARRAY, (z3: Z3Obj) => z3.Array.K],
  [Z3_decl_kind.Z3_OP_EXTRACT, (z3: Z3Obj) => z3.Extract],
  [Z3_decl_kind.Z3_OP_BV2INT, (z3: Z3Obj) => z3.BV2Int],
]);

const SYMMETRIC_OPS = [
  Z3_decl_kind.Z3_OP_IFF,
  Z3_decl_kind.Z3_OP_DISTINCT,
  Z3_decl_kind.Z3_OP_AND,
  Z3_decl_kind.Z3_OP_OR,
  Z3_decl_kind.Z3_OP_BADD,
  Z3_decl_kind.Z3_OP_BMUL,
];

const SIMPLE_SIGNATURE_OPS = [Z3_decl_kind.Z3_OP_BV2INT];

export function apply_z3_op(z3: Z3Obj, op_code: Z3_decl_kind, ...args: any[]) {
  while (args.length === 1 && Array.isArray(args[0])) {
    args = args[0];
  }
  try {
    let res: any = undefined;
    if (COMPARISON_OP_TO_FUNC.has(op_code)) {
      res = COMPARISON_OP_TO_FUNC.get(op_code)(z3)(...args);
    } else if (LOGIC_OP_TO_FUNC.has(op_code)) {
      res = LOGIC_OP_TO_FUNC.get(op_code)(z3)(...args);
    } else if (MATH_OP_TO_FUNC.has(op_code)) {
      res = MATH_OP_TO_FUNC.get(op_code)(z3)(...args);
    } else if (ARRAY_OP_TO_FUNC.has(op_code)) {
      res = ARRAY_OP_TO_FUNC.get(op_code)(z3)(...args);
    } else if (DECL_OP_TO_FUNC.has(op_code)) {
      res = DECL_OP_TO_FUNC.get(op_code)(z3)(...args);
    } else if (PARAMETER_FUNC.has(op_code)) {
      res = PARAMETER_FUNC.get(op_code)(z3)(...args);
    } else {
      throw new Error(`Unknown op code: ${op_code}`);
    }
    return res;
  } catch (e) {
    throw e;
    // throw new Error(`Error while processing op_code ${op_code} with args ${args}`);
  }
}

export function has_subexpr(expr: Expr, subexpr: Expr) {
  const z3 = expr.ctx;
  const new_expr = z3.substitute(expr, [subexpr, z3.Var(0, subexpr.sort)]);
  return new_expr.neqIdentity(expr);
}