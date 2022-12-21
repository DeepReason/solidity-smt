export var OPERATION_TYPE;
(function (OPERATION_TYPE) {
    OPERATION_TYPE["ADD"] = "+";
    OPERATION_TYPE["SUBTRACT"] = "-";
    OPERATION_TYPE["MUL"] = "*";
    OPERATION_TYPE["EXP"] = "**";
    OPERATION_TYPE["DIV"] = "/";
    OPERATION_TYPE["MOD"] = "%";
    OPERATION_TYPE["GT"] = ">";
    OPERATION_TYPE["LT"] = "<";
    OPERATION_TYPE["GE"] = ">=";
    OPERATION_TYPE["LE"] = "<=";
    OPERATION_TYPE["EQUAL"] = "==";
    OPERATION_TYPE["NOT_EQUAL"] = "!=";
    OPERATION_TYPE["AND"] = "&&";
    OPERATION_TYPE["OR"] = "||";
    OPERATION_TYPE["SHIFT_LEFT"] = "<<";
    OPERATION_TYPE["SHIFT_RIGHT"] = ">>";
    OPERATION_TYPE["BIT_AND"] = "&";
    OPERATION_TYPE["BIT_OR"] = "|";
    OPERATION_TYPE["BIT_XOR"] = "^";
    OPERATION_TYPE["TERNARY"] = "?";
    OPERATION_TYPE["ARRAY_ACCESS"] = "array_access";
    OPERATION_TYPE["FUNCTION"] = "FUNCTION";
    OPERATION_TYPE["NOT"] = "!";
    OPERATION_TYPE["BIT_NOT"] = "~";
    OPERATION_TYPE["BEFORE"] = "@before";
    OPERATION_TYPE["AFTER"] = "@after";
    OPERATION_TYPE["INIT"] = "@init";
    OPERATION_TYPE["PARENTHESES"] = "PARENTHESES";
})(OPERATION_TYPE || (OPERATION_TYPE = {}));
export var NodeType;
(function (NodeType) {
    NodeType["INTEGER"] = "integer";
    NodeType["DOUBLE"] = "double";
    NodeType["BOOLEAN"] = "boolean";
    NodeType["UNARY"] = "unary";
    NodeType["BINARY"] = "binary";
    NodeType["MULTI"] = "multi";
    NodeType["IDENTIFIER"] = "identifier";
    NodeType["DOT_ACCESS"] = "dot_access";
    NodeType["CAST"] = "cast";
    NodeType["QUANTIFIER"] = "quantifier";
    NodeType["NOT_IMPLEMENTED"] = "not_implemented";
})(NodeType || (NodeType = {}));
export var QuantifierType;
(function (QuantifierType) {
    QuantifierType["FORALL"] = "forall";
    QuantifierType["EXISTS"] = "exists";
    QuantifierType["UNKNOWN"] = "unknown";
})(QuantifierType || (QuantifierType = {}));
export class LanguageNode extends Object {
    constructor(ctx, nt) {
        super();
        this._parent = null;
        this._ctx = ctx;
        this._nodeType = nt;
    }
    get ctx() {
        return this._ctx;
    }
    set parent(value) {
        this._parent = value;
    }
    get parent() {
        return this._parent;
    }
    get nodeType() {
        return this._nodeType;
    }
}
// Includes Integer, Double, Boolean, and Identifier
export class PredicateNode extends LanguageNode {
    constructor(ctx, nt, v) {
        super(ctx, nt);
        this._value = v;
    }
    get value() {
        return this._value;
    }
}
export class UnaryOperationNode extends LanguageNode {
    get operationType() {
        return this._operationType;
    }
    constructor(ctx, child, op) {
        super(ctx, NodeType.UNARY);
        this._child = child;
        this._operationType = op;
    }
    get child() {
        return this._child;
    }
}
export class BinaryOperationNode extends LanguageNode {
    set binaryOperationType(value) {
        this._binaryOperationType = value;
    }
    get binaryOperationType() {
        return this._binaryOperationType;
    }
    constructor(ctx, l, r, ot) {
        super(ctx, NodeType.BINARY);
        this._left = l;
        this._right = r;
        this._left.parent = this;
        this._right.parent = this;
        this._binaryOperationType = ot;
    }
    get left() {
        return this._left;
    }
    get right() {
        return this._right;
    }
}
export class MultiOperationNode extends LanguageNode {
    set childValues(value) {
        this._childValues = value;
    }
    get childValues() {
        return this._childValues;
    }
    get operationType() {
        return this._operationType;
    }
    constructor(ctx, ot, cv) {
        super(ctx, NodeType.MULTI);
        this._operationType = ot;
        this._childValues = cv;
    }
}
export class DotAccessNode extends LanguageNode {
    constructor(ctx, expr, key) {
        super(ctx, NodeType.DOT_ACCESS);
        this._expr = expr;
        this._key = key;
    }
    get expr() {
        return this._expr;
    }
    get key() {
        return this._key;
    }
}
export class CastNode extends LanguageNode {
    constructor(ctx, expr, newType) {
        super(ctx, NodeType.CAST);
        this._expr = expr;
        this._newType = newType;
    }
    get expr() {
        return this._expr;
    }
    get newType() {
        return this._newType;
    }
}
export class QuantifierNode extends LanguageNode {
    constructor(ctx, quantifierType, decls, body) {
        super(ctx, NodeType.QUANTIFIER);
        this._quantifierType = quantifierType;
        this._decls = decls;
        this._body = body;
    }
    get quantifierType() {
        return this._quantifierType;
    }
    get decls() {
        return this._decls;
    }
    get body() {
        return this._body;
    }
}
export class NotImplementedNode extends LanguageNode {
    get nodeType() {
        throw new Error('Method not implemented.');
    }
}
