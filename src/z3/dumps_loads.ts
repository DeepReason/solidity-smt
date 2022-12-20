import makeZ3, {
  Expr,
  FuncDecl,
  Bool,
  Z3Obj,
} from './z3';
import { Model } from 'z3-solver';

/*
DUMPING EXPRESSIONS
*/

function exprToSolverClaim(expr: Expr): Bool {
  const z3 = expr.ctx;
  return expr.eq(z3.Const('__deepreason_claim_tmp', expr.sort));
}

export function dumps_expr(expr: Expr | Expr[]): string {
  let z3: Z3Obj;
  if (Array.isArray(expr)) {
    if (expr.length === 0) return '';
    z3 = expr[0].ctx;
  } else {
    z3 = expr.ctx;
  }

  const solver = new z3.Solver();
  if (Array.isArray(expr)) {
    for (const e of expr) {
      solver.add(exprToSolverClaim(e));
    }
  } else {
    solver.add(exprToSolverClaim(expr));
  }
  const s = solver.toString();
  return s.replace(/\n/g, ' ');
}

/*
LOADING EXPRESSIONS
*/

export function loads_expr(z3: Z3Obj, expr_str: string): Expr[] | Expr {
  const solver = new z3.Solver();
  solver.fromString(expr_str);

  // The assertions come back in the form <EXPRESSION> == __deepreason_claim_tmp
  // Really we just want the left side but we have this form in order to easily bootstrap
  // off of the implemented Z3 solver which only takes boolean expressions
  const exprs = solver.assertions();

  if (exprs.length() == 1) {
    return exprs.get(0).arg(0);
  }
  return [...exprs.values()].map((e) => e.arg(0));
}

export function loads_func_decl(z3: Z3Obj, dec_str: string): FuncDecl {
  const solver = new z3.Solver();
  solver.fromString(dec_str);

  const exprs = solver.assertions();
  if (exprs.length() != 1) {
    throw new Error('Expected a single assertion from func_decl string');
  }
  return exprs.get(0).arg(0).decl();
}

export async function loads_model(z3: Z3Obj, model_str: string): Promise<Model> {
  const m = new z3.Model();
  for (const dv_str of model_str.trim().split(';')) {
    if (!dv_str) {
      continue;
    }
    const [f_str, val] = dv_str.split(':');
    if (val[0] != '&') {
      m.updateValue(loads_func_decl(z3, f_str), loads_expr(z3, val) as Expr);
    } else {
      const entries = val.slice(1).split('&');
      const else_val = loads_expr(z3, entries.pop()!) as Expr;

      const f = loads_func_decl(z3, f_str);

      const interp = m.addFuncInterp(f, else_val);

      for (const entry of entries) {
        const args = entry.split('->').map(
          (x) => loads_expr(z3, x) as Expr,
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
  loads_model,
};

export default dumps_loads;