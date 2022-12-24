import { BitVec, Bool, Expr } from '../z3/z3';
import { ElementarySolidityExpr, SolidityExpr, SolidityExprType, TranslationContext } from './sharedTypes';
import { castTo } from './valueType';
import {
  elementaryTypeNameToBytes,
  ElementaryVarType,
  isSameSolidityType,
  makeElementarySolidityType,
  solidityTypeToString,
} from '../sol_parsing';
import assert from 'assert';
import { repr_of_expr } from '../z3';

type BitVecBinaryFunc = (left: BitVec, right: BitVec) => Expr;
type BooleanBinaryFunc = (left: Bool, right: Bool) => Expr;
type ExprBinaryFunc = (left: Expr, right: Expr) => Expr;

function makeMatchElementary(left: SolidityExpr, right: SolidityExpr, ctx: TranslationContext) {
  // Comparison between elementary types should be handled here
  if (left.type === SolidityExprType.ELEMENTARY) {
    try {
      right = castTo(right, left.varType, ctx);
    } catch (e) {
      throw new Error(`Cannot compare ${left.ctx!.text} and ${right.ctx!.text}`);
    }
  } else if (right.type === SolidityExprType.ELEMENTARY) {
    try {
      left = castTo(left, right.varType, ctx);
    } catch (e) {
      throw new Error(`Cannot compare ${left.ctx!.text} and ${right.ctx!.text}`);
    }
  }

  if (left.type !== SolidityExprType.ELEMENTARY || right.type !== SolidityExprType.ELEMENTARY) {
    throw new Error(`Cannot compare ${left.ctx!.text} and ${right.ctx!.text}`);
  }
}

function processBitVecOperation(
  leftExpr: SolidityExpr,
  rightExpr: SolidityExpr,
  op: BitVecBinaryFunc | undefined,
  op_name: string = 'unknown',
) {
  function fail() {
    throw Error(
      'Unable to process operation ' + op_name + ' between: ' + leftExpr.ctx!.text + ' ' + rightExpr.ctx!.text,
    );
  }

  if (op === undefined) {
    throw fail();
  }
  if (
    !(
      leftExpr.type === SolidityExprType.ELEMENTARY &&
      rightExpr.type === SolidityExprType.ELEMENTARY &&
      leftExpr.expr.ctx.isBitVec(leftExpr.expr) &&
      rightExpr.expr.ctx.isBitVec(rightExpr.expr)
    )
  ) {
    throw fail();
  }
  if (rightExpr.expr.size() !== leftExpr.expr.size()) {
    throw fail();
  }
  return op!(leftExpr.expr, rightExpr.expr);
}

function processBooleanOperation(
  leftExpr: SolidityExpr,
  rightExpr: SolidityExpr,
  op: BooleanBinaryFunc,
  op_name: string = 'unknown',
) {
  function fail() {
    return Error(
      'Unable to process operation ' + op_name + ' between: ' + leftExpr.ctx!.text + ' ' + rightExpr.ctx!.text,
    );
  }

  if (op === undefined) {
    throw fail();
  }
  if (
    !(
      leftExpr.type === SolidityExprType.ELEMENTARY &&
      leftExpr.expr.ctx.isBool(leftExpr.expr) &&
      rightExpr.type === SolidityExprType.ELEMENTARY &&
      rightExpr.expr.ctx.isBool(rightExpr.expr)
    )
  ) {
    throw fail();
  }
  return op!(leftExpr.expr, rightExpr.expr);
}

export enum NumericOperatorOutputType {
  NUMERIC,
  BOOLEAN,
}

export type BinarySolidityExprOperator = {
  name: string;
  call: (a: SolidityExpr, b: SolidityExpr) => SolidityExpr;
};

export class CastFailure extends Error {
  constructor() {
    super(`Cast failure`);
  }
}

export function castElementaries(
  left: ElementarySolidityExpr,
  right: ElementarySolidityExpr,
  ctx: TranslationContext,
): [ElementarySolidityExpr, ElementarySolidityExpr] {
  let works = true;
  if (!isSameSolidityType(left.varType, right.varType)) {
    const lt = left.varType;
    const rt = right.varType;
    // Handle casting to each other
    if (
      (lt.name.startsWith('int') && rt.name.startsWith('int')) ||
      (lt.name.startsWith('uint') && rt.name.startsWith('uint'))
    ) {
      const leftBytes = elementaryTypeNameToBytes(lt.name);
      const rightBytes = elementaryTypeNameToBytes(rt.name);
      if (leftBytes > rightBytes) {
        right = castTo(right, lt, ctx);
      } else {
        left = castTo(left, rt, ctx);
      }
      const z3 = ctx.z3;
      assert(z3.isBitVec(left.expr) && z3.isBitVec(right.expr));
      assert(left.expr.size() === right.expr.size());
    } else {
      works = false;
    }
  }
  if (!works) throw new CastFailure();
  assert(isSameSolidityType(left.varType, right.varType));

  return [left, right];
}

export function makeNumericOperator(
  ctx: TranslationContext,
  op_name: string,
  signed_bitvec_op: BitVecBinaryFunc | undefined,
  unsigned_bitvec_op: BitVecBinaryFunc | undefined = undefined,
  output: NumericOperatorOutputType = NumericOperatorOutputType.NUMERIC,
): BinarySolidityExprOperator {
  if (unsigned_bitvec_op === undefined) unsigned_bitvec_op = signed_bitvec_op;
  return {
    name: op_name,
    call: (leftExpr: SolidityExpr, rightExpr: SolidityExpr): SolidityExpr => {
      function fail() {
        return Error(
          'Unable to process operation ' + op_name + ' between: ' + leftExpr.ctx!.text + ' ' + rightExpr.ctx!.text,
        );
      }

      if (
        !(
          leftExpr.type === SolidityExprType.ELEMENTARY &&
          rightExpr.type === SolidityExprType.ELEMENTARY &&
          leftExpr.expr.ctx.isBitVec(leftExpr.expr) &&
          rightExpr.expr.ctx.isBitVec(rightExpr.expr)
        )
      ) {
        throw fail();
      }

      try {
        [leftExpr, rightExpr] = castElementaries(leftExpr, rightExpr, ctx);
      } catch (e) {
        throw fail();
      }

      const inputSolidityType = leftExpr.varType;
      let outputSolidityType: ElementaryVarType =
        output == NumericOperatorOutputType.NUMERIC ? inputSolidityType : makeElementarySolidityType('bool');

      let res;
      if (inputSolidityType.name.startsWith('int')) {
        res = processBitVecOperation(leftExpr, rightExpr, signed_bitvec_op, op_name);
      } else if (inputSolidityType.name.startsWith('uint') || inputSolidityType.name === 'address') {
        res = processBitVecOperation(leftExpr, rightExpr, unsigned_bitvec_op, op_name);
      } else {
        throw Error('Cannot perform operation ' + op_name + ' on type: ' + solidityTypeToString(inputSolidityType));
      }
      return {
        type: SolidityExprType.ELEMENTARY,
        expr: res,
        varType: outputSolidityType,
      };
    },
  };
}

export function makeBooleanOperator(
  ctx: TranslationContext,
  op_name: string,
  bool_op: BooleanBinaryFunc,
): BinarySolidityExprOperator {
  return {
    name: op_name,
    call: (leftExpr: SolidityExpr, rightExpr: SolidityExpr): SolidityExpr => {
      if (
        !(
          leftExpr.type === SolidityExprType.ELEMENTARY &&
          rightExpr.type === SolidityExprType.ELEMENTARY &&
          leftExpr.expr.ctx.isBool(leftExpr.expr) &&
          rightExpr.expr.ctx.isBool(rightExpr.expr)
        )
      ) {
        throw fail();
      }

      const res = processBooleanOperation(leftExpr, rightExpr, bool_op, op_name);
      return {
        type: SolidityExprType.ELEMENTARY,
        varType: makeElementarySolidityType('bool'),
        expr: res,
      };
    },
  };
}

export function makeGenericOperator(
  ctx: TranslationContext,
  op_name: string,
  expr_op: ExprBinaryFunc,
): BinarySolidityExprOperator {
  return {
    name: op_name,
    call: (left: SolidityExpr, right: SolidityExpr): SolidityExpr => {
      if (left.type === SolidityExprType.ELEMENTARY && ctx.z3.isBool(left.expr)) {
        const op = makeBooleanOperator(ctx, op_name, expr_op);
        return op.call(left, right);
      } else {
        const op = makeNumericOperator(ctx, op_name, expr_op, expr_op, NumericOperatorOutputType.BOOLEAN);
        return op.call(left, right);
      }
    },
  };
}
