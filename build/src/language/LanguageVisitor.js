import { AbstractParseTreeVisitor } from "antlr4ts/tree/AbstractParseTreeVisitor.js";
import { BinaryOperationNode, CastNode, DotAccessNode, MultiOperationNode, NodeType, NotImplementedNode, OPERATION_TYPE, PredicateNode, QuantifierNode, QuantifierType, UnaryOperationNode, } from './LanguageNode.js';
export class LanguageVisitor extends AbstractParseTreeVisitor {
    defaultResult() {
        return new NotImplementedNode(null, NodeType.NOT_IMPLEMENTED);
    }
    constructor() {
        super();
    }
    makeUnaryOperation(ctx, child, operationStr) {
        let childExpr = this.visit(child);
        let values = Object.values(OPERATION_TYPE).filter(x => '' + x == operationStr);
        return new UnaryOperationNode(ctx, childExpr, values[0]);
    }
    makeBinaryOperation(ctx, l, r, operationStr) {
        let left = this.visit(l);
        let right = this.visit(r);
        let values = Object.values(OPERATION_TYPE).filter(x => '' + x == operationStr);
        return new BinaryOperationNode(ctx, left, right, values[0]);
    }
    makeMultiOperation(ctx, opContexts, opType) {
        let children = opContexts.map(cont => this.visit(cont));
        return new MultiOperationNode(ctx, opType, children);
    }
    visitInt(ctx) {
        return new PredicateNode(ctx, NodeType.INTEGER, BigInt(ctx._value.text));
    }
    visitDouble(ctx) {
        return new PredicateNode(ctx, NodeType.DOUBLE, parseFloat(ctx._value.text));
    }
    visitBoolean(ctx) {
        return new PredicateNode(ctx, NodeType.BOOLEAN, ctx._value.text.toLowerCase() == 'true');
    }
    visitIdentifier(ctx) {
        return new PredicateNode(ctx, NodeType.IDENTIFIER, ctx._value.text);
    }
    visitCompareIneq(ctx) {
        return this.makeBinaryOperation(ctx, ctx._left, ctx._right, ctx._operation.text);
    }
    visitCompareEqDistinct(ctx) {
        return this.makeBinaryOperation(ctx, ctx._left, ctx._right, ctx._operation.text);
    }
    visitMultiplicative(ctx) {
        return this.makeBinaryOperation(ctx, ctx._left, ctx._right, ctx._operation.text);
    }
    visitExponential(ctx) {
        return this.makeBinaryOperation(ctx, ctx._left, ctx._right, OPERATION_TYPE.EXP);
    }
    visitAdditive(ctx) {
        return this.makeBinaryOperation(ctx, ctx._left, ctx._right, ctx._operation.text);
    }
    visitShift(ctx) {
        return this.makeBinaryOperation(ctx, ctx._left, ctx._right, ctx._operation.text);
    }
    visitBitwiseAnd(ctx) {
        return this.makeBinaryOperation(ctx, ctx._left, ctx._right, OPERATION_TYPE.BIT_AND);
    }
    visitBitwiseXor(ctx) {
        return this.makeBinaryOperation(ctx, ctx._left, ctx._right, OPERATION_TYPE.BIT_XOR);
    }
    visitBitwiseOr(ctx) {
        return this.makeBinaryOperation(ctx, ctx._left, ctx._right, OPERATION_TYPE.BIT_OR);
    }
    visitLogicalAnd(ctx) {
        return this.makeBinaryOperation(ctx, ctx._left, ctx._right, OPERATION_TYPE.AND);
    }
    visitLogicalOr(ctx) {
        return this.makeBinaryOperation(ctx, ctx._left, ctx._right, OPERATION_TYPE.OR);
    }
    visitTernary(ctx) {
        return this.makeMultiOperation(ctx, ctx.expr(), OPERATION_TYPE.TERNARY);
    }
    visitArrayAccess(ctx) {
        return this.makeMultiOperation(ctx, ctx.expr(), OPERATION_TYPE.ARRAY_ACCESS);
    }
    visitFunctionCall(ctx) {
        return this.makeMultiOperation(ctx, ctx.expr(), OPERATION_TYPE.FUNCTION);
    }
    visitDotExpression(ctx) {
        return new DotAccessNode(ctx, this.visit(ctx.expr()), ctx.ID());
    }
    visitUnary(ctx) {
        return this.makeUnaryOperation(ctx, ctx._v, ctx._operation.text);
    }
    visitTimeAnnotation(ctx) {
        return this.makeUnaryOperation(ctx, ctx._v, ctx._op.text);
    }
    visitParens(ctx) {
        return this.makeUnaryOperation(ctx, ctx._val, OPERATION_TYPE.PARENTHESES);
    }
    visitCast(ctx) {
        return new CastNode(ctx, this.visit(ctx.expr()), ctx._type.text);
    }
    visitQuantifier(ctx) {
        const quantifier = ctx._quantifier.text;
        const quantifierType = quantifier == 'ForAll'
            ? QuantifierType.FORALL
            : quantifier == 'Exists'
                ? QuantifierType.EXISTS
                : QuantifierType.UNKNOWN;
        const decls = ctx.ELEMENTARY_SOLIDITY_VAR_DECL().map(t => t.text);
        const body = this.visit(ctx.expr());
        return new QuantifierNode(ctx, quantifierType, decls, body);
    }
}
