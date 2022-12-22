import {
  AccessibleSolidityExprType,
  SolidityExpr,
  SolidityExprType,
  TranslationContext,
  ElementarySolidityExpr,
} from './sharedTypes';
import {
  elementaryTypeNameToByte,
  isSameSolidityType,
  makeElementarySolidityType,
  SolidityVarType,
  VarTypeKind,
} from '../sol_parsing';
import { BitVec } from '../z3/z3';
import assert from 'assert';

export function castTo(
  solidityExpr: SolidityExpr,
  solidityType: SolidityVarType,
  ctx: TranslationContext,
): ElementarySolidityExpr {
  if (solidityType.type === VarTypeKind.ElementaryTypeName) {
    const typeBytes = elementaryTypeNameToByte(solidityType.name);
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
      const uncastedBytes = elementaryTypeNameToByte(solidityExpr.varType.name);
      if (typeBytes !== uncastedBytes) {
        if (
          (solidityType.name.startsWith('int') && solidityExpr.varType.name.startsWith('int')) ||
          (solidityType.name.startsWith('uint') && solidityExpr.varType.name.startsWith('uint')) ||
          (solidityType.name.startsWith('bytes') && solidityExpr.varType.name.startsWith('bytes'))
        ) {
          const z3 = ctx.z3;
          assert(z3.isBitVec(solidityExpr.expr));
          let newExpr: BitVec = solidityExpr.expr;
          if (typeBytes > uncastedBytes) {
            if (solidityType.name.startsWith('int')) {
              newExpr = newExpr.add(z3.BitVec.val(2n ** BigInt(uncastedBytes * 8 - 1), uncastedBytes * 8));
            }
            newExpr = z3.Concat(z3.BitVec.val(0, typeBytes * 8 - uncastedBytes * 8), newExpr as BitVec);
            if (solidityType.name.startsWith('int')) {
              newExpr = newExpr.sub(z3.BitVec.val(2n ** BigInt(uncastedBytes * 8 - 1), typeBytes * 8));
            }
          } else {
            newExpr = z3.Extract(typeBytes * 8 - 1, 0, solidityExpr.expr as BitVec);
          }
          return {
            type: SolidityExprType.ELEMENTARY,
            expr: newExpr,
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
