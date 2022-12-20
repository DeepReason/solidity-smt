import { ExprResult, parseExpression } from '../parseExpression';
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
} from '../LanguageNode';

describe('Test parsing text expressions', () => {
  it('Test integer', async () => {
    let val: ExprResult = parseExpression(`1`);

    expect(val.hasError).toEqual(false);
    let node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.INTEGER);
  });

  describe('Test booleans', () => {
    async function testExpr(expr: string, expected: boolean) {
      let val: ExprResult = parseExpression(expr);

      expect(val.hasError).toEqual(false);
      let node: LanguageNode = val.value as LanguageNode;
      expect(node.nodeType).toEqual(NodeType.BOOLEAN);
      expect((node as PredicateNode).value).toEqual(expected);
    }

    it('Test boolean 1', async () => await testExpr(`true`, true));
    it('Test boolean 2', async () => await testExpr(`True`, true));
    it('Test boolean 3', async () => await testExpr(`TRUE`, true));
    it('Test boolean 4', async () => await testExpr(`false`, false));
    it('Test boolean 5', async () => await testExpr(`False`, false));
    it('Test boolean 6', async () => await testExpr(`FALSE`, false));
  });

  describe('Test binary operations', () => {
    async function testBinOp(op: string, expected: OPERATION_TYPE) {
      let val: ExprResult = parseExpression(`a ${op} b`);

      expect(val.hasError).toEqual(false);
      let node: LanguageNode = val.value as LanguageNode;
      expect(node.nodeType).toEqual(NodeType.BINARY);
      let binary = node as BinaryOperationNode;
      expect(binary.binaryOperationType).toEqual(expected);
    }

    it('Test AND', async () => await testBinOp(`&&`, OPERATION_TYPE.AND));
    it('Test OR', async () => await testBinOp(`||`, OPERATION_TYPE.OR));
    it('Test add', async () => await testBinOp(`+`, OPERATION_TYPE.ADD));
    it('Test sub', async () => await testBinOp(`-`, OPERATION_TYPE.SUBTRACT));
    it('Test mul', async () => await testBinOp(`*`, OPERATION_TYPE.MUL));
    it('Test div', async () => await testBinOp(`/`, OPERATION_TYPE.DIV));

    it('Test Bitwise AND', async () => await testBinOp(`&`, OPERATION_TYPE.BIT_AND));
    it('Test Bitwise OR', async () => await testBinOp(`|`, OPERATION_TYPE.BIT_OR));
    it('Test Bitwise XOR', async () => await testBinOp(`^`, OPERATION_TYPE.BIT_XOR));
  });

  it('Test add of mul', async () => {
    let val: ExprResult = parseExpression(`1 * 2 + 3*4`);

    expect(val.hasError).toEqual(false);
    let node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.BINARY);
    let binary = node as BinaryOperationNode;
    expect(binary.binaryOperationType).toEqual(OPERATION_TYPE.ADD);
  });

  it('Test compare of mul', async () => {
    let val: ExprResult = parseExpression(`1 * 2 < 3*4`);

    expect(val.hasError).toEqual(false);
    let node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.BINARY);
    let binary = node as BinaryOperationNode;
    expect(binary.binaryOperationType).toEqual(OPERATION_TYPE.LT);
  });

  it('Test compare of exp', async () => {
    let val: ExprResult = parseExpression(`1 ** 2 < 3 ** 4`);

    expect(val.hasError).toEqual(false);
    let node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.BINARY);
    let binary = node as BinaryOperationNode;
    expect(binary.binaryOperationType).toEqual(OPERATION_TYPE.LT);

    const left = binary.left;
    expect(left.nodeType).toEqual(NodeType.BINARY);
    const right = binary.right;
    expect(right.nodeType).toEqual(NodeType.BINARY);
  });

  it('Test bit xor precedence', async () => {
    let val: ExprResult = parseExpression(`1 ^ 2 + 3 `);

    expect(val.hasError).toEqual(false);
    let node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.BINARY);
    let binary = node as BinaryOperationNode;
    expect(binary.binaryOperationType).toEqual(OPERATION_TYPE.BIT_XOR);
  });

  it('Test ternary', async () => {
    let val: ExprResult = parseExpression(`true ? 1 : 2`);

    expect(val.hasError).toEqual(false);
    let node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.MULTI);
    let binary: MultiOperationNode = node as MultiOperationNode;
    expect(binary.operationType).toEqual(OPERATION_TYPE.TERNARY);
    expect(binary.childValues.map(v => v.nodeType)).toEqual([NodeType.BOOLEAN, NodeType.INTEGER, NodeType.INTEGER]);
  });

  it('Test array', async () => {
    let val: ExprResult = parseExpression(`anArray[x + 7]`);

    expect(val.hasError).toEqual(false);
    let node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.MULTI);
    let binary: MultiOperationNode = node as MultiOperationNode;
    expect(binary.operationType).toEqual(OPERATION_TYPE.ARRAY_ACCESS);

    expect(binary.childValues.map(v => v.nodeType)).toEqual([NodeType.IDENTIFIER, NodeType.BINARY]);
  });

  it('Test function', async () => {
    let val: ExprResult = parseExpression(`func(1, 2, 3)`);

    expect(val.hasError).toEqual(false);
    let node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.MULTI);
    let binary: MultiOperationNode = node as MultiOperationNode;
    expect(binary.operationType).toEqual(OPERATION_TYPE.FUNCTION);

    expect(binary.childValues.map(v => v.nodeType)).toEqual([
      NodeType.IDENTIFIER,
      NodeType.INTEGER,
      NodeType.INTEGER,
      NodeType.INTEGER,
    ]);
  });

  it('Dot function', async () => {
    let val: ExprResult = parseExpression(`dot1.dot2.dot3`);

    expect(val.hasError).toEqual(false);
    let node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.DOT_ACCESS);

    let opNode: DotAccessNode = node as DotAccessNode;
    expect(opNode.expr.nodeType === NodeType.DOT_ACCESS).toBeTruthy();
    expect(opNode.key.text == 'dot3').toBeTruthy();
    let lside = opNode.expr as DotAccessNode;
    expect(lside.expr.nodeType === NodeType.IDENTIFIER).toBeTruthy();
    expect(lside.key.text == 'dot2').toBeTruthy();
    expect((lside.expr as PredicateNode).value === 'dot1').toBeTruthy();
  });

  it('Not test', async () => {
    let val: ExprResult = parseExpression(`!dot1.dot2.dot3`);

    expect(val.hasError).toEqual(false);
    let node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.UNARY);
    let binary: MultiOperationNode = node as MultiOperationNode;
    expect(binary.operationType).toEqual(OPERATION_TYPE.NOT);
  });

  it('Tilda test', async () => {
    let val: ExprResult = parseExpression(`~dot1.dot2.dot3`);

    expect(val.hasError).toEqual(false);
    let node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.UNARY);
    let binary: MultiOperationNode = node as MultiOperationNode;
    expect(binary.operationType).toEqual(OPERATION_TYPE.BIT_NOT);
  });

  it('Test @before', async () => {
    let val: ExprResult = parseExpression(`dot1@before`);

    expect(val.hasError).toEqual(false);
    let node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.UNARY);
    let binary: MultiOperationNode = node as MultiOperationNode;
    expect(binary.operationType).toEqual(OPERATION_TYPE.BEFORE);
  });

  it('Test @after', async () => {
    let val: ExprResult = parseExpression(`dot1@after`);

    expect(val.hasError).toEqual(false);
    let node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.UNARY);
    let binary: MultiOperationNode = node as MultiOperationNode;
    expect(binary.operationType).toEqual(OPERATION_TYPE.AFTER);
  });

  it('Test @init', async () => {
    let val: ExprResult = parseExpression(`dot1@init`);

    expect(val.hasError).toEqual(false);
    let node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.UNARY);
    let binary: MultiOperationNode = node as MultiOperationNode;
    expect(binary.operationType).toEqual(OPERATION_TYPE.INIT);
  });

  it('Test parentheses', async () => {
    let val: ExprResult = parseExpression(`(this.is.a.test.of[parentheses])`);

    expect(val.hasError).toEqual(false);
    let node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.UNARY);
    let binary: MultiOperationNode = node as MultiOperationNode;
    expect(binary.operationType).toEqual(OPERATION_TYPE.PARENTHESES);
  });

  it('Test quantifier', async () => {
    let val: ExprResult = parseExpression(`ForAll([address addr], balance[addr] == addr.balance)`);
    expect(val.hasError).toEqual(false);

    const node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.QUANTIFIER);
    const quantifier: QuantifierNode = node as QuantifierNode;
    expect(quantifier.quantifierType).toEqual(QuantifierType.FORALL);

    expect(quantifier.decls.length).toEqual(1);
    expect(quantifier.decls[0]).toEqual('address addr');

    expect(quantifier.body.nodeType).toEqual(NodeType.BINARY);
  });

  it('Test cast', async () => {
    let val: ExprResult = parseExpression(`int256(x)`);
    expect(val.hasError).toEqual(false);

    const node: LanguageNode = val.value as LanguageNode;
    expect(node.nodeType).toEqual(NodeType.CAST);
    const castNode: CastNode = node as CastNode;
    expect(castNode.newType).toEqual('int256');
    expect(castNode.expr.nodeType).toEqual(NodeType.IDENTIFIER);
  });
});
