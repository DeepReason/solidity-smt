import { ANTLRInputStream, CommonTokenStream, } from 'antlr4ts';
import { ExprLexer } from '../../generated/src/language/ExprLexer.js';
import { ExprParser } from '../../generated/src/language/ExprParser.js';
import { LanguageVisitor } from './LanguageVisitor.js';
class ExpressionsErrorListener {
    constructor() {
        this.errors = [];
    }
    syntaxError(recognizer, offendingSymbol, line, charPositionInLine, message, e) {
        console.log('message>>', message);
        this.errors.push({
            startLineNumber: line,
            endLineNumber: line,
            startColumn: charPositionInLine,
            endColumn: charPositionInLine + 1,
            message,
            code: '1', // This the error code you can customize them as you want
        });
    }
    getErrors() {
        return this.errors;
    }
}
export function parseExpression(text) {
    var chars = new ANTLRInputStream(text);
    const lexer = new ExprLexer(chars);
    var lexerErrorListener = new ExpressionsErrorListener();
    var parserErrorListener = new ExpressionsErrorListener();
    var parserVisitor = new LanguageVisitor();
    lexer.removeErrorListeners();
    lexer.addErrorListener(lexerErrorListener);
    const tokens = new CommonTokenStream(lexer);
    const parser = new ExprParser(tokens);
    parser.removeErrorListeners();
    parser.addErrorListener(parserErrorListener);
    let tree = parser.expr();
    let languageNode = parserVisitor.visit(tree);
    const exprResult = {
        value: languageNode,
        lexResult: 1,
        parseErrors: parserErrorListener.getErrors(),
        lexErrors: lexerErrorListener.getErrors(),
        hasError: lexerErrorListener.getErrors().length > 0 || parserErrorListener.getErrors().length > 0,
    };
    return exprResult;
}
