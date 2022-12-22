import { OperationType } from './LanguageNode';
import { SolidityVarType } from '../sol_parsing/sol_parsing_types';

const precedenceOf: Map<OperationType, number> = new Map<OperationType, number>([
  [OperationType.ARRAY_ACCESS, 0],
  [OperationType.NOT, 1],
  [OperationType.BIT_NOT, 1],
  [OperationType.EXP, 2],
  [OperationType.MUL, 3],
  [OperationType.DIV, 3],
  [OperationType.MOD, 3],
  [OperationType.ADD, 4],
  [OperationType.SUBTRACT, 4],
  [OperationType.SHIFT_LEFT, 5],
  [OperationType.SHIFT_RIGHT, 5],
  [OperationType.LT, 6],
  [OperationType.GT, 6],
  [OperationType.LE, 6],
  [OperationType.GE, 6],
  [OperationType.EQUAL, 7],
  [OperationType.NOT_EQUAL, 7],
  [OperationType.BIT_AND, 8],
  [OperationType.BIT_XOR, 9],
  [OperationType.BIT_OR, 10],
  [OperationType.AND, 11],
  [OperationType.OR, 12],
  [OperationType.TERNARY, 13],
]);

type TranslationResult = {
  text: string;
  lowestPrecedenceOperator: OperationType;
  temporal_tag: string;
  type: SolidityVarType;
};
