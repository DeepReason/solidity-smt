import { ParseResult, parseSolidity, stateVarDeclToBytes, typeNameToString, UserTypeDefinition } from './var_parsing';
import {
  EnumDefinition,
  SourceUnit,
  StateVariableDeclaration,
  StateVariableDeclarationVariable,
  StructDefinition,
} from '@solidity-parser/parser/src/ast-types';
import { ContractDefinition } from '@solidity-parser/parser/dist/src/ast-types';
import assert from 'assert';
import { typeNameToVarType, VarType } from './vartype';

export type StateVarData = {
  contractName: string;
  name: string;
  typeString: string;
  type: VarType;
  bytes: number;
  decl: StateVariableDeclarationVariable;
  slot: [number, number] | undefined;
  intraSlot: [number, number] | undefined;
};

export type SolidityData = {
  result: ParseResult;
  stateVarData: StateVarData[];
};

function getVariableData(astContract: ContractDefinition, astGlobalCustomTypeDefinitions: UserTypeDefinition[]) {
  const astUserTypeDefinitions: UserTypeDefinition[] = [...astGlobalCustomTypeDefinitions];
  const stateVars: StateVarData[] = [];

  for (const node of astContract.subNodes) {
    if (node.type === 'StateVariableDeclaration') {
      for (const varDecl of (node as StateVariableDeclaration).variables) {
        stateVars.push({
          contractName: astContract.name,
          name: varDecl.name!,
          typeString: typeNameToString(varDecl.typeName!),
          type: typeNameToVarType(varDecl.typeName!),
          bytes: 0,
          decl: varDecl,
          slot: undefined,
          intraSlot: undefined,
        });
      }
    }
    if (node.type === 'StructDefinition') {
      astUserTypeDefinitions.push(node as StructDefinition);
    }
    if (node.type === 'EnumDefinition') {
      astUserTypeDefinitions.push(node as EnumDefinition);
    }
  }

  // Compute Variable Slots
  let slot = 0;
  let slotUsage = 0;
  let lastSlot: StateVarData[] = [];

  function flushLastSlot() {
    let slotIdx = 0;
    for (const stateVar of lastSlot) {
      if (lastSlot.length > 1) {
        stateVar.intraSlot = [slotIdx, slotIdx + stateVar.bytes];
      }
      slotIdx += stateVar.bytes;
    }
    lastSlot = [];
  }

  function bumpSlot() {
    if (slotUsage > 0) {
      flushLastSlot();
      slotUsage = 0;
      slot++;
    }
  }

  for (const stateVar of stateVars) {
    stateVar.bytes = stateVarDeclToBytes(stateVar.decl, astUserTypeDefinitions);
    if (stateVar.bytes === 0) {
      continue;
    }

    if (slotUsage + stateVar.bytes > 32) {
      bumpSlot();
    }
    if (stateVar.bytes >= 32) {
      const newSlots = Math.ceil(stateVar.bytes / 32);
      stateVar.slot = [slot, slot + newSlots - 1];
      slot += newSlots;

      // These should already be true, but just in case
      lastSlot = [];
      slotUsage = 0;
    } else {
      stateVar.slot = [slot, slot];
      slotUsage += stateVar.bytes;
      lastSlot.push(stateVar);
    }
  }
  bumpSlot();

  return stateVars;
}

function getGlobalDefinitions(ast: ParseResult) {
  // Contracts are defined in the global scope
  const astContracts: ContractDefinition[] = [];

  // Structs can be defined in the global scope
  const astGlobalCustomTypeDefinitions: UserTypeDefinition[] = [];

  assert(ast !== undefined, 'AST is undefined');
  if (ast !== undefined) {
    for (const node of (ast as SourceUnit).children) {
      if (node.type === 'ContractDefinition') {
        astContracts.push(node as ContractDefinition);
      }
      if (node.type === 'StructDefinition') {
        astGlobalCustomTypeDefinitions.push(node as StructDefinition);
      }
      if (node.type === 'EnumDefinition') {
        astGlobalCustomTypeDefinitions.push(node as EnumDefinition);
      }
    }
  }
  return {
    astContracts,
    astGlobalCustomTypeDefinitions,
  };
}

function getSolidityData(solidity: string, contractName?: string): SolidityData;
function getSolidityData(solidity: ParseResult, contractName?: string): SolidityData;
function getSolidityData(solidity: string | ParseResult, contractName?: string): SolidityData {
  if (typeof solidity === 'string') {
    return getSolidityData(parseSolidity(solidity), contractName);
  }
  const { astContracts, astGlobalCustomTypeDefinitions } = getGlobalDefinitions(solidity);
  assert(
    astContracts.length === 1 || contractName,
    'analyze_solidity.ts:getSolidityData: More than one contract found, please specify contract name',
  );

  const astContract = astContracts.length === 1 ? astContracts[0] : astContracts.find(c => c.name === contractName);
  assert(astContract, 'analyze_solidity.ts:getSolidityData: Contract not found');

  const stateVarData = getVariableData(astContract, astGlobalCustomTypeDefinitions);

  return {
    result: solidity,
    stateVarData: stateVarData,
  };
}

export { getSolidityData };
