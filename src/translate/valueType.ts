import {
  AccessibleSolidityExprType,
  SolidityExpr,
  SolidityExprType,
  TranslationContext,
  ElementarySolidityExpr,
} from './sharedTypes';
import {
  elementaryTypeNameToBytes,
  isSameSolidityType,
  makeElementarySolidityType,
  SolidityVarType,
  VarTypeKind,
} from '../sol_parsing';
import { BitVec } from '../z3/z3';
import assert from 'assert';

export function resizeZ3BitVec<T extends number>(expr: BitVec, newSize: T, signed: boolean = false): BitVec<T> {
  const origSize = expr.size();
  const z3 = expr.ctx;
  if (z3.isBitVecVal(expr)) {
    // Special case to simplify early
    return z3.BitVec.val(expr.value() & BigInt((1n << BigInt(newSize)) - 1n), newSize);
  }
  if (newSize > origSize) {
    if (signed) {
      expr = expr.add(z3.BitVec.val(2n ** BigInt(expr.size() - 1), expr.size()));
    }
    expr = z3.Concat(z3.BitVec.val(0, newSize - origSize), expr);
    if (signed) {
      expr = expr.sub(z3.BitVec.val(2n ** BigInt(expr.size() - 1), expr.size()));
    }
  } else if (newSize < origSize) {
    expr = z3.Extract(newSize - 1, 0, expr);
  }
  return expr as BitVec<T>;
}

export function castTo(
  solidityExpr: SolidityExpr,
  solidityType: SolidityVarType,
  ctx: TranslationContext,
): ElementarySolidityExpr {
  if (solidityType.type === VarTypeKind.ElementaryTypeName) {
    const typeBytes = elementaryTypeNameToBytes(solidityType.name);
    if (solidityExpr.type === SolidityExprType.ACCESSIBLE) {
      if (
        solidityExpr.accessibleType === AccessibleSolidityExprType.CONTRACT &&
        isSameSolidityType(solidityType, makeElementarySolidityType('address'))
      ) {
        return {
          type: SolidityExprType.ELEMENTARY,
          ctx: solidityExpr.ctx,
          expr: solidityExpr.contractAddress,
          varType: solidityType,
        };
      }
    } else if (
      solidityExpr.type === SolidityExprType.ELEMENTARY &&
      solidityExpr.varType.type === VarTypeKind.ElementaryTypeName
    ) {
      const uncastedBytes = elementaryTypeNameToBytes(solidityExpr.varType.name);
      if (typeBytes !== uncastedBytes) {
        if (
          (solidityType.name.startsWith('int') && solidityExpr.varType.name.startsWith('int')) ||
          (solidityType.name.startsWith('uint') && solidityExpr.varType.name.startsWith('uint')) ||
          (solidityType.name.startsWith('bytes') && solidityExpr.varType.name.startsWith('bytes'))
        ) {
          const z3 = ctx.z3;
          assert(z3.isBitVec(solidityExpr.expr));
          return {
            type: SolidityExprType.ELEMENTARY,
            expr: resizeZ3BitVec(solidityExpr.expr, typeBytes * 8, solidityType.name.startsWith('name')),
            varType: solidityType,
          };
        } else {
          throw new Error('Cannot cast directly from ' + solidityExpr.varType.name + ' to ' + solidityType.name);
        }
      }
      return {
        type: SolidityExprType.ELEMENTARY,
        expr: solidityExpr.expr,
        varType: solidityType,
      };
    }
  }
  throw Error('Cannot cast ' + solidityExpr.ctx!.text + ' to type ' + solidityType.type);
}
