import Z3, { Expr, Z3Obj } from '../z3/z3';
import { AnySort, BitVecSort, SMTArray, SMTArraySort, Sort, Z3_ast } from 'z3-solver';
import { AccessibleSolidityExprType, SolidityExpr, SolidityExprType, TranslationContext } from './sharedTypes';
import { ParserRuleContext } from 'antlr4ts';

export type Z3GlobalStorage = SMTArray<
  'main',
  [BitVecSort<160>],
  SMTArraySort<'main', [BitVecSort<256>], BitVecSort<256>>
>;

export type Z3GlobalBalances = SMTArray<'main', [BitVecSort<160>], BitVecSort<256>>;

export type Z3Globals = {
  storage: Z3GlobalStorage;
  balances: Z3GlobalBalances;
};

export function makeZ3GlobalStorage(z3: Z3Obj, tags: string = '__untagged'): Z3GlobalStorage {
  return z3.Array.const(
    'global_storage' + tags,
    z3.BitVec.sort(160),
    z3.Array.sort(z3.BitVec.sort(256), z3.BitVec.sort(256)),
  );
}

export function makeZ3Balances(z3: Z3Obj, tags: string = '__untagged'): Z3GlobalBalances {
  return z3.Array.const('balances' + tags, z3.BitVec.sort(160), z3.BitVec.sort(256));
}

export function makeZ3Globals(z3: Z3Obj, tags: string = '__untagged'): Z3Globals {
  return {
    storage: makeZ3GlobalStorage(z3, tags),
    balances: makeZ3Balances(z3, tags),
  };
}

export function low_level_tag_expr<T extends Expr>(expr: T, newTag: string): T {
  const z3 = expr.ctx;
  return z3.substitute(
    expr,
    [makeZ3GlobalStorage(z3), makeZ3GlobalStorage(z3, newTag)],
    [makeZ3Balances(z3), makeZ3Balances(z3, newTag)],
  ) as T;
}

export function tagSolidityExpr(
  expr: SolidityExpr,
  newTag: string,
  ctx: TranslationContext,
  node_ctx: ParserRuleContext,
): SolidityExpr {
  switch (expr.type) {
    case SolidityExprType.ELEMENTARY:
      return {
        ...expr,
        expr: low_level_tag_expr(expr.expr, newTag),
      };
    case SolidityExprType.MAPPING:
      return {
        ...expr,
        globals: {
          storage: low_level_tag_expr(expr.globals.storage, newTag),
          balances: low_level_tag_expr(expr.globals.balances, newTag),
        },
        contractAddress: low_level_tag_expr(expr.contractAddress, newTag),
        slot: low_level_tag_expr(expr.slot, newTag),
      };
    case SolidityExprType.ARRAY:
      return {
        ...expr,
        globals: {
          storage: low_level_tag_expr(expr.globals.storage, newTag),
          balances: low_level_tag_expr(expr.globals.balances, newTag),
        },
        contractAddress: low_level_tag_expr(expr.contractAddress, newTag),
        slot: low_level_tag_expr(expr.slot, newTag),
      };
    case SolidityExprType.ACCESSIBLE:
      switch (expr.accessibleType) {
        case AccessibleSolidityExprType.CONTRACT:
          return {
            ...expr,
            globals: {
              storage: low_level_tag_expr(expr.globals.storage, newTag),
              balances: low_level_tag_expr(expr.globals.balances, newTag),
            },
            contractAddress: low_level_tag_expr(expr.contractAddress, newTag),
          };
        case AccessibleSolidityExprType.STRUCT:
          return {
            ...expr,
            globals: {
              storage: low_level_tag_expr(expr.globals.storage, newTag),
              balances: low_level_tag_expr(expr.globals.balances, newTag),
            },
            contractAddress: low_level_tag_expr(expr.contractAddress, newTag),
            slot: low_level_tag_expr(expr.slot, newTag),
          };
      }
      break;
  }
  ctx.warnings.push(node_ctx._start.line + ': No effect of @' + newTag + 'tag on ' + expr.ctx?.text);
  return {
    ...expr,
  };
}

export type ASTExpr<Name extends string = 'main', S extends Sort<Name> = AnySort<Name>> = Expr<Name, S, Z3_ast>;
