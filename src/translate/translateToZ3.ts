import { ExprResult, ILanguageError, parseExpression } from '../language/parseExpression';
import { Expr, makeZ3, Z3Obj } from '../z3/z3';
import {
  BinaryOperationNode,
  CastNode,
  DotAccessNode,
  LanguageNode,
  MultiOperationNode,
  NodeType,
  OperationType,
  PredicateNode,
  QuantifierNode,
  QuantifierType,
  UnaryOperationNode,
} from '../language/LanguageNode';
import { ASTExpr, low_level_tag_expr, tagSolidityExpr } from './solidityZ3Generator';
import assert from 'assert';
import { elementaryTypeNameToByte, makeElementarySolidityType, ParsedSolidityData } from '../sol_parsing';
import { loadExposedImmutables } from './exposedImmutables';
import {
  AccessibleSolidityExprType,
  ElementarySolidityExpr,
  SolidityExpr,
  SolidityExprType,
  TranslationContext,
} from './sharedTypes';
import { castTo } from './valueType';
import { accessibleValues, dotAccess, getDefaultContractExpr, getTypeFromObjectId, mappingAccess } from './dotAccess';
import {
  BinarySolidityExprOperator,
  makeBooleanOperator,
  makeNumericOperator,
  NumericOperatorOutputType,
} from './operators';

function fillInitialVarScope(ctx: TranslationContext) {
  const scope = new Map<string, SolidityExpr>();

  // Message identifier
  scope.set('msg', {
    type: SolidityExprType.ACCESSIBLE,
    accessibleType: AccessibleSolidityExprType.MESSAGE,
  });

  ctx.varScope = scope;

  const contract = getDefaultContractExpr(ctx);

  scope.set('this', contract);

  const contractData = ctx.parsedSolidityData.typeObjects[contract.id];
  assert(contractData.type === 'Contract');
  const source = contractData.sourceUnit;

  for (const varName of accessibleValues(contract, ctx)) {
    try {
      scope.set(varName, dotAccess(contract, varName, ctx));
    } catch (e) {
      ctx.warnings.push('skipping variable ' + varName);
    }
  }
  for (const [varName, objectId] of Object.entries(ctx.parsedSolidityData.sourceUnits[source].types)) {
    try {
      scope.set(varName, getTypeFromObjectId(objectId, ctx));
    } catch (e) {
      ctx.warnings.push('skipping variable ' + varName);
    }
  }
}

function nodeToSolidityExpr(node: LanguageNode, ctx: TranslationContext): SolidityExpr {
  return {
    ..._nodeToSolidityExpr(node, ctx),
    ctx: node.ctx!,
  };
}

/*
Doesn't necessarily return the correct context field in SolidityExpr
 */
function _nodeToSolidityExpr(node: LanguageNode, ctx: TranslationContext): SolidityExpr {
  switch (node.nodeType) {
    case NodeType.INTEGER:
      const intNode = node as PredicateNode;
      const v = intNode.value as bigint;
      return {
        type: SolidityExprType.ELEMENTARY,
        expr: ctx.z3.BitVec.val(v, 256),
        varType: makeElementarySolidityType(v >= 0 ? 'uint256' : 'int256'),
      };
    case NodeType.BOOLEAN:
      const boolNode = node as PredicateNode;
      return {
        type: SolidityExprType.ELEMENTARY,
        expr: ctx.z3.Bool.val(boolNode.value as boolean),
        varType: makeElementarySolidityType('bool'),
      };
    case NodeType.IDENTIFIER:
      const identifier = node as PredicateNode;
      const identifierName = identifier.value as string;
      if (ctx.varScope.has(identifierName)) {
        return ctx.varScope.get(identifierName)!;
      }
      throw new Error('Unknown identifier: ' + identifierName);
    case NodeType.DATA_COMPARISON:
      const dataComparison = node as BinaryOperationNode;
      let dataleft = nodeToSolidityExpr(dataComparison.left, ctx);
      let dataright = nodeToSolidityExpr(dataComparison.right, ctx);

      // Comparison between elementary types should be handled here
      if (dataleft.type === SolidityExprType.ELEMENTARY) {
        try {
          dataright = castTo(dataright, dataleft.varType, ctx);
        } catch (e) {
          throw new Error(`Cannot compare ${dataleft.ctx!.text} and ${dataright.ctx!.text}`);
        }
      } else if (dataright.type === SolidityExprType.ELEMENTARY) {
        try {
          dataleft = castTo(dataleft, dataright.varType, ctx);
        } catch (e) {
          throw new Error(`Cannot compare ${dataleft.ctx!.text} and ${dataright.ctx!.text}`);
        }
      }

      if (
        dataleft.type === SolidityExprType.ACCESSIBLE &&
        dataright.type === SolidityExprType.ACCESSIBLE &&
        dataleft.accessibleType === dataright.accessibleType &&
        dataleft.accessibleType !== AccessibleSolidityExprType.MESSAGE
      ) {
        const objectId = dataleft.id;
        const obj = ctx.parsedSolidityData.typeObjects[objectId];
        throw new Error('Unimplemented: comparisons between ' + obj.name);
      }
      if (dataleft.type !== SolidityExprType.ELEMENTARY || dataright.type !== SolidityExprType.ELEMENTARY) {
        throw new Error(`Cannot compare ${dataleft.ctx!.text} and ${dataright.ctx!.text}`);
      }

      switch (dataComparison.binaryOperationType) {
        case OperationType.EQUAL:
          return {
            type: SolidityExprType.ELEMENTARY,
            expr: dataleft.expr.eq(dataright.expr),
            varType: makeElementarySolidityType('bool'),
          };
        case OperationType.NOT_EQUAL:
          return {
            type: SolidityExprType.ELEMENTARY,
            expr: dataleft.expr.neq(dataright.expr),
            varType: makeElementarySolidityType('bool'),
          };
      }
      throw Error(`Operation ${dataComparison.binaryOperationType} not supported`);
    case NodeType.UNARY:
      const unaryNode = node as UnaryOperationNode;
      const opType = unaryNode.operationType;
      const childExpr = nodeToSolidityExpr(unaryNode.child, ctx);
      if ([OperationType.BEFORE, OperationType.AFTER, OperationType.INIT].includes(opType)) {
        return tagSolidityExpr(childExpr, opType, ctx, node.ctx!);
      } else if (opType === OperationType.PARENTHESES) {
        return {
          ...childExpr,
          ctx: node.ctx!,
        };
      } else {
        throw new Error('Unimplemented unary operation: ' + opType);
      }
    case NodeType.BINARY:
      const binaryOp = node as BinaryOperationNode;
      const left = nodeToSolidityExpr(binaryOp.left, ctx);
      const right = nodeToSolidityExpr(binaryOp.right, ctx);

      let op: BinarySolidityExprOperator;

      switch (binaryOp.binaryOperationType) {
        case OperationType.ADD:
          op = makeNumericOperator(ctx, '+', (a, b) => a.add(b));
          break;
        case OperationType.SUBTRACT:
          op = makeNumericOperator(ctx, '-', (a, b) => a.sub(b));
          break;
        case OperationType.MUL:
          op = makeNumericOperator(ctx, '*', (a, b) => a.mul(b));
          break;
        case OperationType.DIV:
          op = makeNumericOperator(
            ctx,
            '/',
            (a, b) => a.sdiv(b),
            (a, b) => a.udiv(b),
          );
          break;
        case OperationType.EXP:
          op = makeNumericOperator(ctx, '**', undefined);
          break;
        case OperationType.GT:
          op = makeNumericOperator(
            ctx,
            '>',
            (a, b) => a.sgt(b),
            (a, b) => a.ugt(b),
            NumericOperatorOutputType.BOOLEAN,
          );
          break;
        case OperationType.LT:
          op = makeNumericOperator(
            ctx,
            '<',
            (a, b) => a.slt(b),
            (a, b) => a.ult(b),
            NumericOperatorOutputType.BOOLEAN,
          );
          break;
        case OperationType.GE:
          op = makeNumericOperator(
            ctx,
            '>=',
            (a, b) => a.sge(b),
            (a, b) => a.uge(b),
            NumericOperatorOutputType.BOOLEAN,
          );
          break;
        case OperationType.LE:
          op = makeNumericOperator(
            ctx,
            '<=',
            (a, b) => a.sle(b),
            (a, b) => a.ule(b),
            NumericOperatorOutputType.BOOLEAN,
          );
          break;
        case OperationType.OR:
          op = makeBooleanOperator(ctx, '||', (a, b) => a.or(b));
          break;
        case OperationType.AND:
          op = makeBooleanOperator(ctx, '&&', (a, b) => a.and(b));
          break;
        case OperationType.BIT_OR:
          op = makeNumericOperator(ctx, '|', undefined, (l, r) => l.or(r));
          break;
        case OperationType.BIT_AND:
          op = makeNumericOperator(ctx, '&', undefined, (l, r) => l.and(r));
          break;
        case OperationType.BIT_XOR:
          op = makeNumericOperator(ctx, '^', undefined, (l, r) => l.xor(r));
          break;
        case OperationType.SHIFT_LEFT:
          op = makeNumericOperator(ctx, '<<', (l, r) => l.shl(r));
          break;
        case OperationType.SHIFT_RIGHT:
          op = makeNumericOperator(
            ctx,
            '>>',
            (l, r) => l.shr(r),
            (l, r) => l.lshr(r),
          );
          break;
        default:
          throw new Error('(nodeToZ3): Unsupported binary operation: ' + binaryOp.binaryOperationType);
      }
      return op.call(left, right);
    case NodeType.MULTI:
      const multiOp = node as MultiOperationNode;
      const children = multiOp.childValues.map(childValue => nodeToSolidityExpr(childValue, ctx));
      switch (multiOp.operationType) {
        case OperationType.ARRAY_ACCESS:
          assert(children.length === 2, 'Array access must have 2 children');
          let array = children[0];
          let index = children[1];

          if (array.type !== SolidityExprType.MAPPING && array.type !== SolidityExprType.ARRAY) {
            throw new Error('Cannot access ' + array.ctx!.text + ' using []');
          }

          if (array.type === SolidityExprType.MAPPING) {
            return mappingAccess(array, index, ctx);
          } else {
            throw Error('Array access not implemented');
          }
      }
      throw Error('Unsupported multi operation: ' + multiOp.operationType);
    case NodeType.DOT_ACCESS:
      const dotAccessNode = node as DotAccessNode;
      const member = dotAccessNode.key.text;
      const accessible = nodeToSolidityExpr(dotAccessNode.expr, ctx);
      return dotAccess(accessible, member, ctx);
    case NodeType.CAST:
      const cast = node as CastNode;
      const origExpr = nodeToSolidityExpr(cast.expr, ctx);
      const solidityType = makeElementarySolidityType(cast.newType);
      return castTo(origExpr, solidityType, ctx);
    case NodeType.QUANTIFIER:
      const quantifier = node as QuantifierNode;
      const newScope = new Map<string, SolidityExpr>(ctx.varScope);

      const declGens: ElementarySolidityExpr[] = [];

      for (const decl of quantifier.decls) {
        const split = decl.split(/\s+/);
        if (split.length !== 2) {
          throw new Error('Invalid variable declaration in quantifier: ' + decl);
        }
        const name = split[1];
        const typeBytes = elementaryTypeNameToByte(split[0]);
        if (typeBytes == 0) {
          throw new Error('Non-elementary type declaration in quantifier: ' + decl);
        }
        if (newScope.has(name)) {
          throw new Error('Variable declaration in quantifier already defined: ' + decl);
        }
        const gen: ElementarySolidityExpr = {
          type: SolidityExprType.ELEMENTARY,
          varType: makeElementarySolidityType(split[0]),
          expr: ctx.z3.BitVec.const(name, typeBytes * 8),
          ctx: quantifier.ctx!,
        };
        newScope.set(name, gen);
        declGens.push(gen);
      }
      assert(declGens.length >= 1);
      const body = nodeToSolidityExpr(quantifier.body, {
        ...ctx,
        varScope: newScope,
      });
      if (body.type !== SolidityExprType.ELEMENTARY || !ctx.z3.isBool(body.expr)) {
        throw new Error('Body of quantifier is not a boolean: ' + body.ctx!.text);
      }
      const qvars = declGens.map(x => x.expr);
      assert(qvars.length >= 1);
      switch (quantifier.quantifierType) {
        case QuantifierType.FORALL:
          return {
            type: SolidityExprType.ELEMENTARY,
            varType: makeElementarySolidityType('bool'),
            expr: ctx.z3.ForAll(qvars as [ASTExpr, ...ASTExpr[]], body.expr),
          };
        case QuantifierType.EXISTS:
          return {
            type: SolidityExprType.ELEMENTARY,
            varType: makeElementarySolidityType('bool'),
            expr: ctx.z3.Exists(qvars as [ASTExpr, ...ASTExpr[]], body.expr),
          };
      }
  }
  throw new Error('Unsupported parsed node type: ' + node.nodeType);
}

export function parseResultToZ3(parseResult: ExprResult, ctx: TranslationContext): Expr {
  let node: LanguageNode = parseResult.value as LanguageNode;
  fillInitialVarScope(ctx);

  let solidityExpr = nodeToSolidityExpr(node, ctx);
  switch (solidityExpr.type) {
    case SolidityExprType.TYPE:
      throw new Error('Expression is not a value');
    case SolidityExprType.MAPPING:
      throw new Error('Expression is a mapping');
    case SolidityExprType.ARRAY:
      throw new Error('Expression is an array');
    case SolidityExprType.ACCESSIBLE:
      throw new Error('Expression is a ' + solidityExpr.accessibleType);
    case SolidityExprType.ELEMENTARY:
      break;
  }
  const expr = solidityExpr.expr;
  return low_level_tag_expr(expr, '');
}

export async function translateToZ3(
  text: string,
  contractName: string,
  parsedSolidityData: ParsedSolidityData,
  exposedImmutablesJSON: any,
  z3?: Z3Obj,
): Promise<any> {
  try {
    const parsedInput = parseExpression(text);

    if (parsedInput.hasError) {
      function getNiceMessage(e: ILanguageError) {
        const msg = e.message;
        const missingTokenPattern = /mismatched input '(.*)?' expecting (.*)?/;
        if (missingTokenPattern.test(msg)) {
          const match = missingTokenPattern.exec(msg);
          if (match) {
            const [, unexpected, expected] = match;
            return `Unexpected token ${unexpected}`;
          }
        }
        const emptyQVarsPattern = /missing ELEMENTARY_SOLIDITY_VAR_DECL at ']'/;
        if (emptyQVarsPattern.test(msg)) {
          return 'No quantified variables provided';
        }
        return msg;
      }

      return {
        error: parsedInput.parseErrors.map(getNiceMessage).join('\n'),
      };
    }

    if (!z3) {
      z3 = await makeZ3();
    }

    const exposedImmutables = loadExposedImmutables(z3, exposedImmutablesJSON);
    const ctx: TranslationContext = {
      contractName,
      parsedSolidityData,
      exposedImmutables,
      warnings: [],
      varScope: new Map(),
      z3,
    };
    const expr = parseResultToZ3(parsedInput, ctx);

    return {
      expr: expr,
      warnings: ctx.warnings,
    };
  } catch (e) {
    console.error(e);
    return {
      error: '' + e,
    };
  }
}
