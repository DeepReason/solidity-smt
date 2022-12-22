import { ParserRuleContext } from 'antlr4ts';
import { TerminalNode } from 'antlr4ts/tree';

export enum OperationType {
  ADD = '+',
  SUBTRACT = '-',
  MUL = '*',
  EXP = '**',
  DIV = '/',
  MOD = '%',
  GT = '>',
  LT = '<',
  GE = '>=',
  LE = '<=',
  EQUAL = '==',
  NOT_EQUAL = '!=',
  AND = '&&',
  OR = '||',
  SHIFT_LEFT = '<<',
  SHIFT_RIGHT = '>>',
  BIT_AND = '&',
  BIT_OR = '|',
  BIT_XOR = '^',
  TERNARY = '?',
  ARRAY_ACCESS = 'array_access',
  FUNCTION = 'FUNCTION',
  NOT = '!',
  BIT_NOT = '~',
  BEFORE = '@before',
  AFTER = '@after',
  INIT = '@init',
  PARENTHESES = 'PARENTHESES',
}

export enum NodeType {
  INTEGER = 'integer',
  DOUBLE = 'double',
  BOOLEAN = 'boolean',

  UNARY = 'unary',
  BINARY = 'binary',
  MULTI = 'multi',

  IDENTIFIER = 'identifier',

  DOT_ACCESS = 'dot_access',
  CAST = 'cast',
  QUANTIFIER = 'quantifier',

  DATA_COMPARISON = 'data_comparison',

  NOT_IMPLEMENTED = 'not_implemented',
}

export enum QuantifierType {
  FORALL = 'forall',
  EXISTS = 'exists',
  UNKNOWN = 'unknown',
}

export abstract class LanguageNode extends Object {
  private _parent: LanguageNode | null = null;
  protected _nodeType: NodeType;
  protected _ctx: ParserRuleContext | null;

  constructor(ctx: ParserRuleContext | null, nt: NodeType) {
    super();
    this._ctx = ctx;
    this._nodeType = nt;
  }

  public get ctx(): ParserRuleContext | null {
    return this._ctx;
  }

  public set parent(value: LanguageNode | null) {
    this._parent = value;
  }

  public get parent(): LanguageNode | null {
    return this._parent;
  }

  public get nodeType(): NodeType {
    return this._nodeType;
  }
}

// Includes Integer, Double, Boolean, and Identifier
export class PredicateNode extends LanguageNode {
  private _value: Object;

  constructor(ctx: ParserRuleContext | null, nt: NodeType, v: Object) {
    super(ctx, nt);
    this._value = v;
  }

  public get value() {
    return this._value;
  }
}

export class UnaryOperationNode extends LanguageNode {
  private _child: LanguageNode;
  private _operationType: OperationType;

  public get operationType(): OperationType {
    return this._operationType;
  }

  constructor(ctx: ParserRuleContext | null, child: LanguageNode, op: OperationType) {
    super(ctx, NodeType.UNARY);

    this._child = child;
    this._operationType = op;
  }

  public get child(): LanguageNode {
    return this._child;
  }
}

export class BinaryOperationNode extends LanguageNode {
  private readonly _left: LanguageNode;
  private readonly _right: LanguageNode;

  private _binaryOperationType: OperationType;
  public set binaryOperationType(value: OperationType) {
    this._binaryOperationType = value;
  }

  public get binaryOperationType(): OperationType {
    return this._binaryOperationType;
  }

  constructor(
    ctx: ParserRuleContext | null,
    l: LanguageNode,
    r: LanguageNode,
    ot: OperationType,
    nt: NodeType.BINARY | NodeType.DATA_COMPARISON = NodeType.BINARY,
  ) {
    super(ctx, nt);
    this._left = l;
    this._right = r;
    this._left.parent = this;
    this._right.parent = this;
    this._binaryOperationType = ot;
  }

  public get left(): LanguageNode {
    return this._left;
  }

  public get right(): LanguageNode {
    return this._right;
  }
}

export class MultiOperationNode extends LanguageNode {
  private _operationType: OperationType;
  private _childValues: LanguageNode[];
  public set childValues(value: LanguageNode[]) {
    this._childValues = value;
  }

  public get childValues(): LanguageNode[] {
    return this._childValues;
  }

  public get operationType(): OperationType {
    return this._operationType;
  }

  constructor(ctx: ParserRuleContext | null, ot: OperationType, cv: Array<LanguageNode>) {
    super(ctx, NodeType.MULTI);

    this._operationType = ot;
    this._childValues = cv;
  }
}

export class DotAccessNode extends LanguageNode {
  private readonly _expr: LanguageNode;
  private readonly _key: TerminalNode;

  constructor(ctx: ParserRuleContext | null, expr: LanguageNode, key: TerminalNode) {
    super(ctx, NodeType.DOT_ACCESS);

    this._expr = expr;
    this._key = key;
  }

  public get expr(): LanguageNode {
    return this._expr;
  }

  public get key(): TerminalNode {
    return this._key;
  }
}

export class CastNode extends LanguageNode {
  private readonly _expr: LanguageNode;
  private readonly _newType: string;

  constructor(ctx: ParserRuleContext | null, expr: LanguageNode, newType: string) {
    super(ctx, NodeType.CAST);

    this._expr = expr;
    this._newType = newType;
  }

  public get expr(): LanguageNode {
    return this._expr;
  }

  public get newType(): string {
    return this._newType;
  }
}

export class QuantifierNode extends LanguageNode {
  private readonly _quantifierType: QuantifierType;
  private readonly _decls: string[];
  private readonly _body: LanguageNode;

  constructor(ctx: ParserRuleContext | null, quantifierType: QuantifierType, decls: string[], body: LanguageNode) {
    super(ctx, NodeType.QUANTIFIER);

    this._quantifierType = quantifierType;
    this._decls = decls;
    this._body = body;
  }

  public get quantifierType(): QuantifierType {
    return this._quantifierType;
  }

  public get decls(): string[] {
    return this._decls;
  }

  public get body(): LanguageNode {
    return this._body;
  }
}

export class NotImplementedNode extends LanguageNode {
  public get nodeType(): NodeType {
    throw new Error('Method not implemented.');
  }
}
