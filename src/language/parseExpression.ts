import {
  ANTLRErrorListener,
  ANTLRInputStream,
  CharStream,
  CommonTokenStream,
  RecognitionException,
  Recognizer,
} from 'antlr4ts';
import { ExprLexer } from '../../generated/src/language/ExprLexer';
import { ExprContext, ExprParser } from '../../generated/src/language/ExprParser';

import { LanguageNode } from './LanguageNode';
import { LanguageVisitor } from './LanguageVisitor';

export interface ILanguageError {
  startLineNumber: number;
  startColumn: number;
  endLineNumber: number;
  endColumn: number;
  message: string;
  code: string;
}

export interface ExprResult {
  value: LanguageNode | null;
  lexResult: any;
  parseErrors: ILanguageError[];
  lexErrors: ILanguageError[];
  hasError: boolean;
}

class ExpressionsErrorListener implements ANTLRErrorListener<any> {
  private errors: ILanguageError[] = [];

  syntaxError(
    recognizer: Recognizer<any, any>,
    offendingSymbol: any,
    line: number,
    charPositionInLine: number,
    message: string,
    e: RecognitionException | undefined,
  ): void {
    console.log('message>>', message);
    this.errors.push({
      startLineNumber: line,
      endLineNumber: line,
      startColumn: charPositionInLine,
      endColumn: charPositionInLine + 1, //Let's suppose the length of the error is only 1 char for simplicity
      message,
      code: '1', // This the error code you can customize them as you want
    });
  }

  getErrors(): ILanguageError[] {
    return this.errors;
  }
}

export function parseExpression(text: string): ExprResult {
  var chars: CharStream = new ANTLRInputStream(text);

  const lexer = new ExprLexer(chars);

  var lexerErrorListener: ExpressionsErrorListener = new ExpressionsErrorListener();
  var parserErrorListener: ExpressionsErrorListener = new ExpressionsErrorListener();

  var parserVisitor: LanguageVisitor = new LanguageVisitor();
  lexer.removeErrorListeners();
  lexer.addErrorListener(lexerErrorListener);
  const tokens = new CommonTokenStream(lexer);

  const parser = new ExprParser(tokens);
  parser.removeErrorListeners();

  parser.addErrorListener(parserErrorListener);

  let tree: ExprContext = parser.expr();
  let languageNode: LanguageNode | null = parserVisitor.visit(tree);

  const exprResult: ExprResult = {
    value: languageNode,
    lexResult: 1,
    parseErrors: parserErrorListener.getErrors(),
    lexErrors: lexerErrorListener.getErrors(),
    hasError: lexerErrorListener.getErrors().length > 0 || parserErrorListener.getErrors().length > 0,
  };
  return exprResult;
}
