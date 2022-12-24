import { BitVec, Expr } from 'z3-solver';
import { ArrayVarType, ElementaryVarType, MappingVarType, ParsedSolidityData } from '../sol_parsing';
import { ExposedImmutables } from './exposedImmutables';
import { Z3Obj } from '../z3';
import { ParserRuleContext } from 'antlr4ts';
import { UserDefinedTypeKind } from '../sol_parsing/sol_parsing_types';
import { Z3Globals } from './solidityZ3Generator';

export enum SolidityExprType {
  ELEMENTARY = 'Elementary',
  MAPPING = 'Mapping',
  ARRAY = 'Array',
  ACCESSIBLE = 'Accessible',
  TYPE = 'Type',
}

export enum AccessibleSolidityExprType {
  CONTRACT = 'Contract',
  STRUCT = 'Struct',
  MESSAGE = 'Message',
}

type SolidityExprBase = {
  type: SolidityExprType;
  ctx?: ParserRuleContext;
};

export type ElementarySolidityExpr = SolidityExprBase & {
  type: SolidityExprType.ELEMENTARY;
  expr: Expr;
  varType: ElementaryVarType;
};

export type MappingSolidityExpr = SolidityExprBase & {
  type: SolidityExprType.MAPPING;
  globals: Z3Globals;
  contractAddress: BitVec<160>;
  slot: BitVec<256>;
  varType: MappingVarType;
};

export type ArraySolidityExpr = SolidityExprBase & {
  type: SolidityExprType.ARRAY;
  globals: Z3Globals;
  contractAddress: BitVec<160>;
  slot: BitVec<256>;
  varType: ArrayVarType;
};

export type AccessibleSolidityExprBase = SolidityExprBase & {
  type: SolidityExprType.ACCESSIBLE;
  accessibleType: AccessibleSolidityExprType;
};

export type ContractSolidityExpr = AccessibleSolidityExprBase & {
  accessibleType: AccessibleSolidityExprType.CONTRACT;
  id: number;
  globals: Z3Globals;
  contractAddress: BitVec<160>;
};

export type StructSolidityExpr = AccessibleSolidityExprBase & {
  accessibleType: AccessibleSolidityExprType.STRUCT;
  id: number;
  globals: Z3Globals;
  contractAddress: BitVec<160>;
  slot: BitVec<256>;
  offset: number;
};

export type MessageSolidityExpr = AccessibleSolidityExprBase & {
  accessibleType: AccessibleSolidityExprType.MESSAGE;
};

export type AccessibleSolidityExpr = ContractSolidityExpr | StructSolidityExpr | MessageSolidityExpr;

export type TypeSolidityExpr = SolidityExprBase & {
  type: SolidityExprType.TYPE;
  typeType: UserDefinedTypeKind;
  id: number;
};

export type SolidityExpr =
  | ElementarySolidityExpr
  | MappingSolidityExpr
  | ArraySolidityExpr
  | TypeSolidityExpr
  | AccessibleSolidityExpr;

export type TranslationContext = {
  contractName: string;
  parsedSolidityData: ParsedSolidityData;
  exposedImmutables: ExposedImmutables;
  warnings: string[];
  varScope: Map<string, SolidityExpr>;
  z3: Z3Obj;
};
