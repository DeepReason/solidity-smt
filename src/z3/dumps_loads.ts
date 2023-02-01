import makeZ3, {
  Expr,
  FuncDecl,
  Bool,
  Z3Obj
} from "./z3";
import { Model, Quantifier } from "z3-solver";

/*
DUMPING EXPRESSIONS
*/

export function dumps_expr(expr: Expr | Expr[]): string {
  let z3: Z3Obj;
  if (Array.isArray(expr)) {
    if (expr.length === 0) return "(declare-fun __deepreason__placeholder__ () Bool) (assert __deepreason__placeholder__)";
    z3 = expr[0].ctx;
  } else {
    z3 = expr.ctx;
  }

  const solver = new z3.Solver();
  if (Array.isArray(expr)) {
    const claim = z3.Function.declare(
      "__deepreason__placeholder__",
        ...expr.map(e => e.sort),
        z3.Bool.sort()
      ).call(...expr);
    solver.add(
      claim
    );
  } else {
    solver.add(
      z3.Function.declare(
        "__deepreason__placeholder__",
        expr.sort,
        z3.Bool.sort()
      ).call(expr)
    );
  }
  const s = solver.toString();
  return s.replace(/\s/g, " ");
}

/*
LOADING EXPRESSIONS
*/

export function loads_expr(z3: Z3Obj, expr_str: string, force_list: boolean = false): Expr[] | Expr {
  const solver = new z3.Solver();
  solver.fromString(expr_str);

  const exprs = solver.assertions();
  if (exprs.length() !== 1) {
    throw new Error(`Expected 1 assertion in expr_str, got ${exprs.length}`);
  }

  const expr = exprs.get(0);
  if (expr.numArgs() == 1 && !force_list) {
    return expr.arg(0);
  }
  return expr.children();
}

export function loads_func_decl(z3: Z3Obj, dec_str: string): FuncDecl {
  const solver = new z3.Solver();
  solver.fromString(dec_str);

  const exprs = solver.assertions();
  if (exprs.length() != 1) {
    throw new Error("Expected a single assertion from func_decl string");
  }
  return exprs.get(0).arg(0).decl();
}

export async function loads_model(z3: Z3Obj, model_str: string): Promise<Model> {
  const m = new z3.Model();
  for (const dv_str of model_str.trim().split(";")) {
    if (!dv_str) {
      continue;
    }
    const [f_str, val] = dv_str.split("::");
    if (val[0] != "&") {
      m.updateValue(loads_func_decl(z3, f_str), loads_expr(z3, val) as Expr);
    } else {
      const entries = val.slice(1).split("&");
      let else_val = loads_expr(z3, entries.pop()!) as Expr;
      if (z3.isQuantifier(else_val)) {
        else_val = else_val.body();
      }

      const f = loads_func_decl(z3, f_str);

      const interp = m.addFuncInterp(f, else_val);

      for (const entry of entries) {
        const args = entry.split("->").map(
          (x) => loads_expr(z3, x) as Expr
        );
        const v = args.pop()!;
        interp.addEntry(args, v);
      }
    }
  }
  return m;
}

const dumps_loads = {
  dumps_expr: dumps_expr,
  loads_expr: loads_expr,
  loads_model
};

export default dumps_loads;