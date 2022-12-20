import { Expr } from 'z3-solver';
import { Z3SolidityGenerators } from '../sol_parsing/solidityZ3Generator';
import { OPERATION_TYPE } from './LanguageNode';
import { SolidityData } from '../sol_parsing/analyze_solidity';
import { VarType } from '../sol_parsing/vartype';

const precedenceOf: Map<OPERATION_TYPE, number> = new Map<OPERATION_TYPE, number>([
  [OPERATION_TYPE.ARRAY_ACCESS, 0],
  [OPERATION_TYPE.NOT, 1],
  [OPERATION_TYPE.BIT_NOT, 1],
  [OPERATION_TYPE.EXP, 2],
  [OPERATION_TYPE.MUL, 3],
  [OPERATION_TYPE.DIV, 3],
  [OPERATION_TYPE.MOD, 3],
  [OPERATION_TYPE.ADD, 4],
  [OPERATION_TYPE.SUBTRACT, 4],
  [OPERATION_TYPE.SHIFT_LEFT, 5],
  [OPERATION_TYPE.SHIFT_RIGHT, 5],
  [OPERATION_TYPE.LT, 6],
  [OPERATION_TYPE.GT, 6],
  [OPERATION_TYPE.LE, 6],
  [OPERATION_TYPE.GE, 6],
  [OPERATION_TYPE.EQUAL, 7],
  [OPERATION_TYPE.NOT_EQUAL, 7],
  [OPERATION_TYPE.BIT_AND, 8],
  [OPERATION_TYPE.BIT_XOR, 9],
  [OPERATION_TYPE.BIT_OR, 10],
  [OPERATION_TYPE.AND, 11],
  [OPERATION_TYPE.OR, 12],
  [OPERATION_TYPE.TERNARY, 13]
]);

type TranslationResult = {
  text: string,
  lowestPrecedenceOperator: OPERATION_TYPE,
  temporal_tag: string,
  type: VarType
}

export function Z3ToText(expr: Expr, solidityData: Z3SolidityGenerators): string {
  return '';
}