import { Token } from 'antlr4ts';
import { AbstractParseTreeVisitor } from 'antlr4ts/tree/AbstractParseTreeVisitor';
import {
  AdditiveContext,
  ArrayAccessContext,
  BitwiseAndContext,
  BitwiseOrContext,
  BitwiseXorContext,
  BooleanContext,
  CastContext,
  CompareIneqContext,
  DataComparisonContext,
  DotExpressionContext,
  ExponentialContext,
  ExprContext,
  FunctionCallContext,
  IdentifierContext,
  IntContext,
  LogicalAndContext,
  LogicalOrContext,
  MultiplicativeContext,
  ParensContext,
  QuantifierContext,
  ShiftContext,
  TernaryContext,
  TimeAnnotationContext,
  UnaryContext,
} from '../../generated/src/language/ExprParser';
import { ExprVisitor } from '../../generated/src/language/ExprVisitor';

import {
  BinaryOperationNode,
  CastNode,
  DotAccessNode,
  LanguageNode,
  MultiOperationNode,
  NodeType,
  NotImplementedNode,
  OperationType,
  PredicateNode,
  QuantifierNode,
  QuantifierType,
  UnaryOperationNode,
} from './LanguageNode';

export class LanguageVisitor extends AbstractParseTreeVisitor<LanguageNode> implements ExprVisitor<LanguageNode> {
  protected defaultResult(): LanguageNode {
    return new NotImplementedNode(null, NodeType.NOT_IMPLEMENTED);
  }

  constructor() {
    super();
  }

  private makeUnaryOperation(ctx: ExprContext, child: ExprContext, operationStr: string) {
    let childExpr = this.visit(child);

    let values: Array<OperationType> = Object.values(OperationType).filter(x => '' + x == operationStr);

    return new UnaryOperationNode(ctx, childExpr, values[0]);
  }

  private makeBinaryOperation(
    ctx: ExprContext,
    l: ExprContext,
    r: ExprContext,
    operationStr: string,
    nt: NodeType.BINARY | NodeType.DATA_COMPARISON = NodeType.BINARY,
  ) {
    let left = this.visit(l);
    let right = this.visit(r);

    let values: Array<OperationType> = Object.values(OperationType).filter(x => '' + x == operationStr);

    return new BinaryOperationNode(ctx, left, right, values[0], nt);
  }

  private makeMultiOperation(ctx: ExprContext, opContexts: Array<ExprContext>, opType: OperationType) {
    let children: Array<LanguageNode> = opContexts.map(cont => this.visit(cont));
    return new MultiOperationNode(ctx, opType, children);
  }

  visitInt(ctx: IntContext) {
    return new PredicateNode(ctx, NodeType.INTEGER, BigInt(ctx._value.text as string));
  }

  visitBoolean(ctx: BooleanContext) {
    return new PredicateNode(ctx, NodeType.BOOLEAN, (ctx._value.text as string).toLowerCase() == 'true');
  }

  visitIdentifier(ctx: IdentifierContext) {
    return new PredicateNode(ctx, NodeType.IDENTIFIER, ctx._value.text as string);
  }

  visitCompareIneq(ctx: CompareIneqContext) {
    return this.makeBinaryOperation(ctx, ctx._left, ctx._right, ctx._operation.text as string);
  }

  visitDataComparison(ctx: DataComparisonContext) {
    return this.makeBinaryOperation(
      ctx,
      ctx._left,
      ctx._right,
      ctx._operation.text as string,
      NodeType.DATA_COMPARISON,
    );
  }

  visitMultiplicative(ctx: MultiplicativeContext) {
    return this.makeBinaryOperation(ctx, ctx._left, ctx._right, ctx._operation.text as string);
  }

  visitExponential(ctx: ExponentialContext) {
    return this.makeBinaryOperation(ctx, ctx._left, ctx._right, OperationType.EXP as string);
  }

  visitAdditive(ctx: AdditiveContext) {
    return this.makeBinaryOperation(ctx, ctx._left, ctx._right, ctx._operation.text as string);
  }

  visitShift(ctx: ShiftContext) {
    return this.makeBinaryOperation(ctx, ctx._left, ctx._right, ctx._operation.text as string);
  }

  visitBitwiseAnd(ctx: BitwiseAndContext) {
    return this.makeBinaryOperation(ctx, ctx._left, ctx._right, OperationType.BIT_AND);
  }

  visitBitwiseXor(ctx: BitwiseXorContext) {
    return this.makeBinaryOperation(ctx, ctx._left, ctx._right, OperationType.BIT_XOR);
  }

  visitBitwiseOr(ctx: BitwiseOrContext) {
    return this.makeBinaryOperation(ctx, ctx._left, ctx._right, OperationType.BIT_OR);
  }

  visitLogicalAnd(ctx: LogicalAndContext) {
    return this.makeBinaryOperation(ctx, ctx._left, ctx._right, OperationType.AND);
  }

  visitLogicalOr(ctx: LogicalOrContext) {
    return this.makeBinaryOperation(ctx, ctx._left, ctx._right, OperationType.OR);
  }

  visitTernary(ctx: TernaryContext) {
    return this.makeMultiOperation(ctx, ctx.expr(), OperationType.TERNARY);
  }

  visitArrayAccess(ctx: ArrayAccessContext) {
    return this.makeMultiOperation(ctx, ctx.expr(), OperationType.ARRAY_ACCESS);
  }

  visitFunctionCall(ctx: FunctionCallContext) {
    return this.makeMultiOperation(ctx, ctx.expr(), OperationType.FUNCTION);
  }

  visitDotExpression(ctx: DotExpressionContext) {
    return new DotAccessNode(ctx, this.visit(ctx.expr()), ctx.ID()!);
  }

  visitUnary(ctx: UnaryContext) {
    return this.makeUnaryOperation(ctx, ctx._v, (ctx._operation as Token).text as string);
  }

  visitTimeAnnotation(ctx: TimeAnnotationContext) {
    return this.makeUnaryOperation(ctx, ctx._v, (ctx._op as Token).text as string);
  }

  visitParens(ctx: ParensContext) {
    return this.makeUnaryOperation(ctx, ctx._val, OperationType.PARENTHESES);
  }

  visitCast(ctx: CastContext) {
    return new CastNode(ctx, this.visit(ctx.expr()), ctx._type.text!);
  }

  visitQuantifier(ctx: QuantifierContext) {
    const quantifier = ctx._quantifier.text as string;
    const quantifierType =
      quantifier == 'ForAll'
        ? QuantifierType.FORALL
        : quantifier == 'Exists'
        ? QuantifierType.EXISTS
        : QuantifierType.UNKNOWN;
    const decls = ctx.ELEMENTARY_SOLIDITY_VAR_DECL().map(t => t.text!);
    const body = this.visit(ctx.expr());

    return new QuantifierNode(ctx, quantifierType, decls, body);
  }
}
