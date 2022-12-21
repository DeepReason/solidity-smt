import { ExprResult, parseExpression } from '../language/parseExpression';
import { Arith, BitVec, Bool, Expr, Z3Obj } from '../z3/z3';
import {
  BinaryOperationNode,
  CastNode,
  DotAccessNode,
  LanguageNode,
  MultiOperationNode,
  NodeType,
  OPERATION_TYPE,
  PredicateNode,
  QuantifierNode,
  QuantifierType,
  UnaryOperationNode,
} from '../language/LanguageNode';
import {
  AnnotatedExpr,
  AnnotatedMappingZ3,
  AnnotatedZ3,
  GlobalStorageZ3,
  isAnnotatedZ3,
  isAnnotatedZ3Expr,
  isAnnotatedZ3Mapping,
  makeZ3Balances,
  makeZ3GlobalStorage,
  AnnotatedZ3Generator,
  Z3SolidityGenerators,
  AnnotatedExprGenerator,
  ASTExpr,
} from './solidityZ3Generator';
import { repr_of_expr } from '../z3/repr';
import assert from 'assert';
import {
  ElementaryVarType,
  isSameType,
  makeElementaryVarType,
  VarTypeKind,
  varTypeToString,
} from '../sol_parsing/vartype';
import { elementaryTypeNameToByte } from '../sol_parsing/var_parsing';
import { ParserRuleContext } from 'antlr4ts';
import { dumps_expr } from '../z3/dumps_loads';

function castToSolidityType(
  uncasted: AnnotatedZ3 | number | bigint | boolean,
  solidityType: ElementaryVarType,
  z3: Z3Obj,
): AnnotatedExpr {
  if (isAnnotatedZ3(uncasted) && !isAnnotatedZ3Expr(uncasted)) {
    throw new Error('Cannot only cast elementary types');
  }
  const typeBytes = elementaryTypeNameToByte(solidityType.name); // Also throws if the type is invalid
  let toCast;
  if (isAnnotatedZ3Expr(uncasted)) {
    assert(uncasted.solidityType.type === VarTypeKind.ElementaryTypeName);
    const uncastedType = uncasted.solidityType;
    const uncastedBytes = elementaryTypeNameToByte(uncastedType.name);
    toCast = uncasted.expr;
    if (typeBytes !== uncastedBytes) {
      if (
        (solidityType.name.startsWith('int') && uncastedType.name.startsWith('int')) ||
        (solidityType.name.startsWith('uint') && uncastedType.name.startsWith('uint'))
      ) {
        if (typeBytes > uncastedBytes) {
          toCast = z3.Concat(
            z3.BitVec.val(solidityType.name[0] == 'u' ? 0 : -1, typeBytes * 8 - uncastedBytes * 8),
            toCast as BitVec,
          );
        } else {
          toCast = z3.Extract(typeBytes * 8 - 1, 0, toCast as BitVec);
        }
      } else {
        throw new Error(
          'ERROR: Cannot cast from ' + JSON.stringify(uncastedType.name) + ' to ' + JSON.stringify(solidityType.name),
        );
      }
    }
  } else {
    if (solidityType.name === 'bool') {
      if (typeof uncasted !== 'boolean') {
        throw new Error('Cannot cast to bool: ' + uncasted);
      }
      toCast = z3.Bool.val(uncasted);
    } else {
      if (typeof uncasted !== 'bigint' || !Number.isInteger(uncasted)) {
        throw new Error('Cannot cast to int: ' + uncasted);
      }
      toCast = z3.BitVec.val(uncasted, typeBytes * 8);
    }
  }
  return {
    solidityType,
    expr: toCast,
  };
}

type ArithBinaryFunc = (left: Arith, right: Arith) => Expr;
type BitVecBinaryFunc = (left: BitVec, right: BitVec) => Expr;
type BooleanBinaryFunc = (left: Bool, right: Bool) => Expr;
type ExprBinaryFunc = (left: Expr, right: Expr) => Expr;
type LiteralFunc = (left: any, right: any) => any;

function processArithOperation(
  leftExpr: any,
  rightExpr: any,
  arith_op: ArithBinaryFunc | undefined,
  z3: Z3Obj,
  op_name: string = 'unknown',
) {
  if (z3.isArith(leftExpr) && z3.isArith(rightExpr)) {
    if (arith_op === undefined) {
      throw new Error(
        'Unable to process arithmetic operation ' +
          op_name +
          ' between Arith: ' +
          repr_of_expr(leftExpr) +
          ' ' +
          repr_of_expr(rightExpr),
      );
    }
    return arith_op(leftExpr as Arith, rightExpr as Arith);
  } else if (z3.isArith(leftExpr) && typeof rightExpr === 'number') {
    return arith_op!(leftExpr as Arith, z3.Real.val(rightExpr));
  } else if (z3.isArith(rightExpr) && typeof leftExpr === 'number') {
    return arith_op!(z3.Real.val(leftExpr), rightExpr as Arith);
  }

  throw new Error('Unable to process arithmetic operation ' + op_name + ' between: ' + leftExpr + ' ' + rightExpr);
}

function processBitVecOperation(
  leftExpr: any,
  rightExpr: any,
  bitvec_op: BitVecBinaryFunc | undefined,
  z3: Z3Obj,
  op_name: string = 'unknown',
) {
  if ((z3.isBitVec(leftExpr) || z3.isBitVec(rightExpr)) && bitvec_op === undefined) {
    throw new Error('No implementation for bitvec operation ' + op_name);
  }
  if (z3.isBitVec(leftExpr) && z3.isBitVec(rightExpr)) {
    if (rightExpr.size() != leftExpr.size()) {
      throw new Error(
        '(nodeToZ3): left and right bitvec sizes are not equal:\n' +
          'left (' +
          leftExpr.size() +
          ') size: ' +
          repr_of_expr(leftExpr) +
          '\n' +
          'right (' +
          rightExpr.size() +
          ') size: ' +
          repr_of_expr(rightExpr),
      );
    }
    return bitvec_op!(leftExpr as BitVec, rightExpr as BitVec);
  } else if (z3.isBitVec(leftExpr) && typeof rightExpr === 'bigint') {
    return bitvec_op!(leftExpr as BitVec, z3.BitVec.val(rightExpr, leftExpr.size()));
  } else if (z3.isBitVec(rightExpr) && typeof leftExpr === 'bigint') {
    return bitvec_op!(z3.BitVec.val(leftExpr, rightExpr.size()), rightExpr as BitVec);
  }

  throw new Error('Unable to process bitvec operation ' + op_name + ' between: ' + leftExpr + ' ' + rightExpr);
}

function processBooleanOperation(
  leftExpr: any,
  rightExpr: any,
  op: BooleanBinaryFunc,
  z3: Z3Obj,
  op_name: string = 'unknown',
) {
  if (z3.isBool(leftExpr) && z3.isBool(rightExpr)) {
    return op(leftExpr as Bool, rightExpr as Bool);
  }

  throw new Error('Unable to process boolean operation ' + op_name + ' between: ' + leftExpr + ' ' + rightExpr);
}

enum NumericOperatorOutputType {
  NUMERIC,
  BOOLEAN,
}

type AnnotatedZ3Operator = {
  name: string;
  call: (left: any, right: any, z3: Z3Obj) => AnnotatedExpr | AnnotatedMappingZ3 | number | bigint | boolean;
};

function makeNumericOperator(
  context: ParserRuleContext,
  op_name: string,
  literal_op: LiteralFunc | undefined,
  arith_op: ArithBinaryFunc | undefined,
  signed_bitvec_op: BitVecBinaryFunc | undefined,
  unsigned_bitvec_op: BitVecBinaryFunc | undefined = undefined,
  output: NumericOperatorOutputType = NumericOperatorOutputType.NUMERIC,
): AnnotatedZ3Operator {
  const ContextualizedError = (msg: string) => new Error(context.text + ':\n' + msg);

  if (unsigned_bitvec_op === undefined) unsigned_bitvec_op = signed_bitvec_op;
  return {
    name: op_name,
    call: (left: any, right: any, z3: Z3Obj) => {
      if (isAnnotatedZ3(left) && isAnnotatedZ3(right)) {
        let works = true;
        if (
          left.solidityType.type !== VarTypeKind.ElementaryTypeName ||
          right.solidityType.type !== VarTypeKind.ElementaryTypeName
        ) {
          works = false;
        } else if (left.solidityType.name !== right.solidityType.name) {
          // Handle casting to each other
          if (
            (left.solidityType.name.startsWith('int') && right.solidityType.name.startsWith('int')) ||
            (left.solidityType.name.startsWith('uint') && right.solidityType.name.startsWith('uint'))
          ) {
            const leftBytes = elementaryTypeNameToByte(left.solidityType.name);
            const rightBytes = elementaryTypeNameToByte(right.solidityType.name);
            if (leftBytes > rightBytes) {
              right = castToSolidityType(right, left.solidityType, z3);
            } else {
              left = castToSolidityType(left, right.solidityType, z3);
            }
          } else {
            works = false;
          }
        }
        if (!works) {
          throw ContextualizedError(
            'Unable to perform operation `' +
              op_name +
              '` between objects of type ' +
              varTypeToString(left.solidityType) +
              ' and ' +
              varTypeToString(right.solidityType),
          );
        }
      }
      const leftExpr = isAnnotatedZ3(left) ? (left as AnnotatedExpr).expr : left;
      const rightExpr = isAnnotatedZ3(right) ? (right as AnnotatedExpr).expr : right;

      if (!z3.isExpr(leftExpr) && typeof leftExpr !== 'number' && typeof leftExpr !== 'bigint') {
        throw ContextualizedError('Left side of operation is not a valid input to ' + op_name);
      }

      if (!z3.isExpr(rightExpr) && typeof rightExpr !== 'number' && typeof rightExpr !== 'bigint') {
        throw ContextualizedError('Right side of operation is not a valid input to ' + op_name);
      }

      if (!z3.isExpr(leftExpr) && !z3.isExpr(rightExpr)) {
        if (literal_op !== undefined) return literal_op(leftExpr, rightExpr);
        throw ContextualizedError('Cannot perform operation ' + op_name + ' on untyped inputs');
      }

      const inputSolidityType = (
        isAnnotatedZ3(left) ? left.solidityType : (right as AnnotatedExpr).solidityType
      ) as ElementaryVarType;

      let outputSolidityType: ElementaryVarType =
        output == NumericOperatorOutputType.NUMERIC ? inputSolidityType : makeElementaryVarType('bool');

      let res;
      if (z3.isArith(leftExpr) || z3.isArith(rightExpr)) {
        res = processArithOperation(leftExpr, rightExpr, arith_op, z3, op_name);
      } else {
        assert(z3.isBitVec(leftExpr) || z3.isBitVec(rightExpr));
        if (inputSolidityType.name.startsWith('int')) {
          res = processBitVecOperation(leftExpr, rightExpr, signed_bitvec_op, z3, op_name);
        } else if (inputSolidityType.name.startsWith('uint') || inputSolidityType.name === 'address') {
          res = processBitVecOperation(leftExpr, rightExpr, unsigned_bitvec_op, z3, op_name);
        } else {
          throw ContextualizedError(
            'Cannot perform operation ' + op_name + ' on type: ' + varTypeToString(inputSolidityType),
          );
        }
      }
      return {
        solidityType: outputSolidityType,
        expr: res,
      };
    },
  };
}

function makeBooleanOperator(
  context: ParserRuleContext,
  op_name: string,
  literal_op: LiteralFunc | undefined,
  bool_op: BooleanBinaryFunc,
): AnnotatedZ3Operator {
  const ContextualizedError = (msg: string) => new Error(context.text + ':\n' + msg);

  return {
    name: op_name,
    call: (left: any, right: any, z3: Z3Obj) => {
      const leftExpr = isAnnotatedZ3(left) ? (left as AnnotatedExpr).expr : left;
      const rightExpr = isAnnotatedZ3(right) ? (right as AnnotatedExpr).expr : right;

      if (!z3.isExpr(leftExpr) && typeof leftExpr !== 'boolean') {
        throw ContextualizedError('Left side of operation is not a valid input to ' + op_name);
      }

      if (!z3.isExpr(rightExpr) && typeof rightExpr !== 'boolean') {
        throw ContextualizedError('Right side of operation is not a valid input to ' + op_name);
      }

      if (!z3.isExpr(leftExpr) && !z3.isExpr(rightExpr)) {
        if (literal_op !== undefined) return literal_op(leftExpr, rightExpr);
        throw ContextualizedError('Cannot perform operation ' + op_name + ' on untyped inputs');
      }

      const res = processBooleanOperation(leftExpr, rightExpr, bool_op, z3, op_name);
      return {
        solidityType: makeElementaryVarType('bool'),
        expr: res,
      };
    },
  };
}

function makeGenericOperator(
  context: ParserRuleContext,
  op_name: string,
  literal_op: LiteralFunc | undefined,
  expr_op: ExprBinaryFunc,
): AnnotatedZ3Operator {
  return {
    name: op_name,
    call: (left: any, right: any, z3: Z3Obj) => {
      if (typeof left === 'boolean' || (isAnnotatedZ3Expr(left) && z3.isBool(left.expr))) {
        const op = makeBooleanOperator(context, op_name, literal_op, expr_op);
        return op.call(left, right, z3);
      } else {
        const op = makeNumericOperator(
          context,
          op_name,
          literal_op,
          expr_op,
          expr_op,
          expr_op,
          NumericOperatorOutputType.BOOLEAN,
        );
        return op.call(left, right, z3);
      }
    },
  };
}

class Identifier {
  private readonly _name: string;

  constructor(name: string) {
    this._name = name;
  }
}

type Generator = (
  z3: Z3Obj,
  global_storage: GlobalStorageZ3,
) => AnnotatedExpr | AnnotatedMappingZ3 | Identifier | number | bigint | boolean;

type Scope = Map<string, Generator>;

function createDefaultScope(solidityData: Z3SolidityGenerators): Scope {
  // Create Default Scope
  const scope = new Map<string, Generator>();
  // Message identifier
  scope.set('msg', (z3, gs) => new Identifier('msg'));
  // Storage variables
  for (const [key, generator] of solidityData.globalVarZ3Generators.entries()) {
    scope.set(key, generator);
  }
  return scope;
}

function nodeToZ3(node: LanguageNode, scope: Scope): Generator {
  switch (node.nodeType) {
    case NodeType.INTEGER:
      const intNode = node as PredicateNode;
      return (z3, gs) => intNode.value as bigint;
    case NodeType.DOUBLE:
      const doubleNode = node as PredicateNode;
      return (z3, gs) => doubleNode.value as number;
    case NodeType.BOOLEAN:
      const boolNode = node as PredicateNode;
      return (z3, gs) => boolNode.value as boolean;
    case NodeType.IDENTIFIER:
      const identifier = node as PredicateNode;
      const nodeVarName = identifier.value as string;
      if (!scope.has(nodeVarName)) {
        throw new Error('Unknown identifier: ' + nodeVarName);
      }
      return scope.get(nodeVarName)!;
    case NodeType.UNARY:
      const unaryNode = node as UnaryOperationNode;
      const opType = unaryNode.operationType;
      const child_gen = nodeToZ3(unaryNode.child, scope);
      if ([OPERATION_TYPE.BEFORE, OPERATION_TYPE.AFTER, OPERATION_TYPE.INIT].includes(opType)) {
        return (z3, gs) => child_gen(z3, makeZ3GlobalStorage(z3, opType));
      } else if (opType === OPERATION_TYPE.PARENTHESES) {
        return child_gen;
      } else {
        throw new Error('Unknown unary operation type: ' + opType);
      }
    case NodeType.BINARY:
      const binaryOp = node as BinaryOperationNode;
      let left_gen = nodeToZ3(binaryOp.left, scope);
      let right_gen = nodeToZ3(binaryOp.right, scope);

      const context = binaryOp.ctx!;

      let op: AnnotatedZ3Operator;

      switch (binaryOp.binaryOperationType) {
        case OPERATION_TYPE.ADD:
          op = makeNumericOperator(
            context,
            '+',
            (a, b) => a + b,
            (a, b) => a.add(b),
            (a, b) => a.add(b),
          );
          break;
        case OPERATION_TYPE.SUBTRACT:
          op = makeNumericOperator(
            context,
            '-',
            (a, b) => a - b,
            (a, b) => a.sub(b),
            (a, b) => a.sub(b),
          );
          break;
        case OPERATION_TYPE.MUL:
          op = makeNumericOperator(
            context,
            '*',
            (a, b) => a * b,
            (a, b) => a.mul(b),
            (a, b) => a.mul(b),
          );
          break;
        case OPERATION_TYPE.DIV:
          op = makeNumericOperator(
            context,
            '/',
            (a, b) => a / b,
            (a, b) => a.div(b),
            (a, b) => a.sdiv(b),
            (a, b) => a.udiv(b),
          );
          break;
        case OPERATION_TYPE.EXP:
          op = makeNumericOperator(
            context,
            '**',
            (a, b) => a ** b,
            (a, b) => a.pow(b),
            undefined,
          );
          break;
        case OPERATION_TYPE.GT:
          op = makeNumericOperator(
            context,
            '>',
            (a, b) => a > b,
            (a, b) => a.gt(b),
            (a, b) => a.sgt(b),
            (a, b) => a.ugt(b),
            NumericOperatorOutputType.BOOLEAN,
          );
          break;
        case OPERATION_TYPE.LT:
          op = makeNumericOperator(
            context,
            '<',
            (a, b) => a < b,
            (a, b) => a.lt(b),
            (a, b) => a.slt(b),
            (a, b) => a.ult(b),
            NumericOperatorOutputType.BOOLEAN,
          );
          break;
        case OPERATION_TYPE.GE:
          op = makeNumericOperator(
            context,
            '>=',
            (a, b) => a >= b,
            (a, b) => a.ge(b),
            (a, b) => a.sge(b),
            (a, b) => a.uge(b),
            NumericOperatorOutputType.BOOLEAN,
          );
          break;
        case OPERATION_TYPE.LE:
          op = makeNumericOperator(
            context,
            '<=',
            (a, b) => a <= b,
            (a, b) => a.le(b),
            (a, b) => a.sle(b),
            (a, b) => a.ule(b),
            NumericOperatorOutputType.BOOLEAN,
          );
          break;
        case OPERATION_TYPE.EQUAL:
          op = makeGenericOperator(
            context,
            '==',
            (a, b) => a === b,
            (a, b) => a.eq(b),
          );
          break;
        case OPERATION_TYPE.NOT_EQUAL:
          op = makeGenericOperator(
            context,
            '!=',
            (a, b) => a !== b,
            (a, b) => a.neq(b),
          );
          break;
        case OPERATION_TYPE.OR:
          op = makeBooleanOperator(
            context,
            '||',
            (a, b) => a || b,
            (a, b) => a.or(b),
          );
          break;
        case OPERATION_TYPE.AND:
          op = makeBooleanOperator(
            context,
            '&&',
            (a, b) => a && b,
            (a, b) => a.and(b),
          );
          break;
        case OPERATION_TYPE.BIT_OR:
          op = makeNumericOperator(
            context,
            '|',
            (a, b) => a | b,
            undefined,
            (l, r) => l.or(r),
          );
          break;
        case OPERATION_TYPE.BIT_AND:
          op = makeNumericOperator(
            context,
            '&',
            (a, b) => a & b,
            undefined,
            (l, r) => l.and(r),
          );
          break;
        case OPERATION_TYPE.BIT_XOR:
          op = makeNumericOperator(
            context,
            '^',
            (a, b) => a ^ b,
            undefined,
            (l, r) => l.xor(r),
          );
          break;
        case OPERATION_TYPE.SHIFT_LEFT:
          op = makeNumericOperator(
            context,
            '<<',
            undefined,
            undefined,
            (l, r) => l.shl(r),
            (l, r) => l.shl(r),
          );
          break;
        case OPERATION_TYPE.SHIFT_RIGHT:
          op = makeNumericOperator(
            context,
            '>>',
            undefined,
            undefined,
            (l, r) => l.shr(r),
            (l, r) => l.lshr(r),
          );
          break;
        default:
          throw new Error('(nodeToZ3): Unsupported binary operation: ' + binaryOp.binaryOperationType);
      }
      return (z3, gs) => {
        return op.call(left_gen(z3, gs), right_gen(z3, gs), z3);
      };
    case NodeType.MULTI:
      const multiOp = node as MultiOperationNode;
      const children = multiOp.childValues.map(childValue => nodeToZ3(childValue, scope));
      switch (multiOp.operationType) {
        case OPERATION_TYPE.ARRAY_ACCESS:
          if (children.length !== 2) {
            throw new Error('Array access must have 2 children');
          }
          let array_gen = children[0];
          let array_string = multiOp.childValues[0].ctx?.text;
          let index_gen = children[1];
          let index_string = multiOp.childValues[1].ctx?.text;
          return (z3, gs) => {
            const array = array_gen(z3, gs);
            const index = index_gen(z3, gs);
            // test if array is a typescript function
            if (!isAnnotatedZ3Mapping(array)) {
              throw new Error('Cannot perform access on object: ' + array);
            }
            const mp = array as AnnotatedMappingZ3;

            if (index instanceof Identifier || isAnnotatedZ3Mapping(index)) {
              throw new Error('Cannot perform access on object: ' + array);
            }
            if (isAnnotatedZ3Expr(index) && !isSameType(index.solidityType, mp.solidityType.keyType)) {
              throw new Error(
                'Array `' +
                  array_string +
                  '` has access type `' +
                  varTypeToString(mp.solidityType.keyType) +
                  '` but index `' +
                  index_string +
                  '` has type `' +
                  varTypeToString(index.solidityType) +
                  '`',
              );
            }

            let idx: Expr | boolean | bigint | number = isAnnotatedZ3Expr(index) ? index.expr : index;
            let idxExpr: Expr = z3.isExpr(idx) ? idx : mp.indexSort.cast(idx);
            assert(z3.isBitVec(idxExpr) || z3.isBool(idxExpr));
            if (idxExpr.sort.neqIdentity(mp.indexSort)) {
              throw new Error(
                'WARNING: Array access with incompatible array and index:\n' +
                  'array: ' +
                  array +
                  '\nindex: ' +
                  idxExpr,
              );
            }
            return mp.get(idxExpr);
          };
        default:
          throw new Error('(nodeToZ3): Unsupported multi operation: ' + multiOp.operationType);
      }
    case NodeType.DOT_ACCESS:
      const dotAccess = node as DotAccessNode;
      const struct_gen = nodeToZ3(dotAccess.expr, scope);
      const struct_text = dotAccess.expr.ctx?.text;
      const field = dotAccess.key.text;
      return (z3, gs) => {
        const struct = struct_gen(z3, gs);
        if (struct instanceof Identifier) {
          if (field === 'sender') {
            return {
              solidityType: makeElementaryVarType('address'),
              expr: z3.BitVec.const('sender', 160),
            };
          } else {
            throw new Error('Invalid field access on msg: ' + field);
          }
        } else if (
          isAnnotatedZ3Expr(struct) &&
          struct.solidityType.type === VarTypeKind.ElementaryTypeName &&
          struct.solidityType.name === 'address' &&
          field === 'balance'
        ) {
          return {
            solidityType: makeElementaryVarType('uint256'),
            expr: makeZ3Balances(z3).select(struct.expr as BitVec<160>),
          };
        } else {
          throw new Error(`\`${field}\` is not an element of \`${struct_text}\``);
        }
      };
    case NodeType.CAST:
      const cast = node as CastNode;
      const uncasted_gen = nodeToZ3(cast.expr, scope);
      return (z3, gs) => {
        const uncasted = uncasted_gen(z3, gs);
        const solidityType = makeElementaryVarType(cast.newType);
        if (uncasted instanceof Identifier) {
          throw new Error('Cannot cast identifier: ' + uncasted);
        }
        return castToSolidityType(uncasted, solidityType, z3);
      };
    case NodeType.QUANTIFIER:
      const quantifier = node as QuantifierNode;
      const newScope = new Map<string, Generator>(scope);
      const declGens: AnnotatedExprGenerator[] = [];
      for (const decl of quantifier.decls) {
        const split = decl.split(/\s+/);
        if (split.length !== 2) {
          throw new Error('(nodeToZ3): Invalid variable declaration in quantifier: ' + decl);
        }
        const name = split[1];
        const typeBytes = elementaryTypeNameToByte(split[0]);
        if (typeBytes == 0) {
          throw new Error('(nodeToZ3): Non-elementary type declaration in quantifier: ' + decl);
        }
        const gen = (z3: Z3Obj, gs: GlobalStorageZ3) => ({
          solidityType: makeElementaryVarType(split[0]),
          expr: z3.BitVec.const(name, typeBytes * 8),
        });
        if (newScope.has(name)) {
          throw new Error('(nodeToZ3): Variable declaration in quantifier already defined: ' + decl);
        }
        newScope.set(name, gen);
        declGens.push(gen);
      }
      assert(declGens.length >= 1);
      const quantifier_gen = nodeToZ3(quantifier.body, newScope);
      switch (quantifier.quantifierType) {
        case QuantifierType.FORALL:
          return (z3, gs) => {
            const body = quantifier_gen(z3, gs);
            if (!isAnnotatedZ3Expr(body)) {
              throw new Error('(nodeToZ3): Quantifier body must be an expression: ' + body);
            }
            if (!z3.isBool(body.expr)) {
              throw new Error('(nodeToZ3): expression is not a boolean: ' + quantifier.body.ctx?.text);
            }
            const qvars = declGens.map(gen => gen(z3, gs).expr);
            assert(qvars.length >= 1);
            return {
              solidityType: makeElementaryVarType('bool'),
              expr: z3.ForAll(qvars as [ASTExpr, ...ASTExpr[]], body.expr),
            };
          };
      }
    default:
      throw new Error('(nodeToZ3): Unsupported node type: ' + node.nodeType);
  }
}

export function parseResultToZ3(parseResult: ExprResult, z3: Z3Obj, solidityData: Z3SolidityGenerators): Expr {
  let node: LanguageNode = parseResult.value as LanguageNode;

  const res = nodeToZ3(node, createDefaultScope(solidityData));
  const annotatedZ3Expr = res(z3, makeZ3GlobalStorage(z3));
  if (!isAnnotatedZ3Expr(annotatedZ3Expr)) {
    throw new Error('(convertZ3): Result is not an annotated expression: ' + annotatedZ3Expr);
  }

  return annotatedZ3Expr.expr;
}

export function textToZ3(text: string, z3: Z3Obj, solidityData: Z3SolidityGenerators): Expr {
  return parseResultToZ3(parseExpression(text), z3, solidityData);
}
