import { stateVarDeclToBytes, typeNameToString, userTypeDefinitionToBytes } from './var_parsing';
import {
  ASTNode,
  ASTReader,
  ContractDefinition,
  EnumDefinition,
  SourceUnit,
  StructDefinition,
  VariableDeclaration,
} from 'solc-typed-ast';
import { typeNameToSolidityType } from './vartype';
import { ContractVarData, ParsedSolidityData, SlotInfo, StructVarData, UserDefinedTypeKind } from './sol_parsing_types';

class SlotCalculator {
  private slot: number = 0;
  private slotUsage: number = 0;
  private lastSlot: [SlotInfo, number][] = [];

  constructor() {}

  flushLastSlot() {
    let slotIdx = 0;
    for (const slotInfo of this.lastSlot) {
      if (this.lastSlot.length > 1) {
        slotInfo[0].intraSlot = [slotIdx, slotIdx + slotInfo[1]];
      }
      slotIdx += slotInfo[1];
    }
    this.lastSlot = [];
  }

  bumpSlot() {
    if (this.slotUsage > 0) {
      this.flushLastSlot();
      this.slotUsage = 0;
      this.slot++;
    }
  }

  addVar(slotInfo: SlotInfo, varDecl: VariableDeclaration) {
    const bytes = stateVarDeclToBytes(varDecl);
    if (bytes === 0) return;
    if (this.slotUsage + bytes > 32) {
      this.bumpSlot();
    }
    if (bytes >= 32) {
      const newSlots = Math.ceil(bytes / 32);
      slotInfo.slot = [this.slot, this.slot + newSlots - 1];
      this.slot += newSlots;

      // These should already be true, but just in case
      this.lastSlot = [];
      this.slotUsage = 0;
    } else {
      slotInfo.slot = [this.slot, this.slot];
      this.slotUsage += bytes;
      this.lastSlot.push([slotInfo, bytes]);
    }
  }

  finish() {
    this.bumpSlot();
  }
}

function getContractVarData(astContract: ContractDefinition): {
  [varName: string]: ContractVarData;
} {
  const stateVars: {
    [varName: string]: ContractVarData;
  } = {};

  const slotCalculator = new SlotCalculator();

  for (const varD of astContract.vStateVariables) {
    const slotInfo: SlotInfo = {
      slot: [0, 0],
      intraSlot: undefined,
    };
    stateVars[varD.name] = {
      name: varD.name,
      typeString: typeNameToString(varD.vType!),
      type: typeNameToSolidityType(varD.vType!),
      bytes: 0,
      slot: slotInfo,
      id: varD.id,
      mutability: varD.mutability,
    };
    slotCalculator.addVar(slotInfo, varD);
  }
  slotCalculator.finish();

  return stateVars;
}

function getStructVarData(astStruct: StructDefinition): {
  [varName: string]: StructVarData;
} {
  const structVars: {
    [varName: string]: StructVarData;
  } = {};

  const slotCalculator = new SlotCalculator();

  for (const varD of astStruct.vMembers) {
    const slotInfo: SlotInfo = {
      slot: [0, 0],
      intraSlot: undefined,
    };
    structVars[varD.name] = {
      name: varD.name,
      typeString: typeNameToString(varD.vType!),
      type: typeNameToSolidityType(varD.vType!),
      bytes: 0,
      slot: slotInfo,
      id: varD.id,
    };
    slotCalculator.addVar(slotInfo, varD);
  }
  slotCalculator.finish();

  return structVars;
}

function getSolidityDataFromSourceUnits(solcOutputSources: SourceUnit[]): ParsedSolidityData {
  const solidityData: ParsedSolidityData = {
    contractId: {},
    sourceUnits: {},
    typeObjects: {},
  };

  for (const sourceUnit of solcOutputSources) {
    for (const contractDefinition of sourceUnit.vContracts) {
      const contractName = contractDefinition.name!;
      solidityData.typeObjects[contractDefinition.id] = {
        type: UserDefinedTypeKind.CONTRACT,
        sourceUnit: sourceUnit.absolutePath,
        name: contractName,
        id: contractDefinition.id,
        subtypes: getSubTypes(contractDefinition),
        vars: getContractVarData(contractDefinition),
      };
      solidityData.contractId[contractName] = contractDefinition.id;
    }
  }

  for (const sourceUnit of solcOutputSources) {
    const absolutePath = sourceUnit.absolutePath;
    const types: { [typeName: string]: number } = {};

    for (const contractDef of sourceUnit.vContracts) {
      types[contractDef.name!] = contractDef.id;
    }
    for (const structDef of sourceUnit.vStructs) {
      types[structDef.name!] = structDef.id;
    }
    for (const enumDef of sourceUnit.vEnums) {
      types[enumDef.name!] = enumDef.id;
    }
    for (const importDirective of sourceUnit.vImportDirectives) {
      importDirective.vSourceUnit.vExportedSymbols.forEach((symbol, name) => {
        types[name] = symbol.id;
      });
    }

    solidityData.sourceUnits[absolutePath] = {
      contracts: sourceUnit.vContracts.map(contractDef => contractDef.id!),
      types,
    };
  }

  function getSubTypes(node: ASTNode): {
    [typeName: string]: number;
  } {
    const res: {
      [typeName: string]: number;
    } = {};
    for (const child of node.children) {
      if (['ContractDefinition', 'StructDefinition', 'EnumDefinition'].includes(child.type)) {
        const castedChild = child as ContractDefinition | StructDefinition | EnumDefinition;
        res[castedChild.name!] = castedChild.id;
      }
    }
    return res;
  }

  if (solcOutputSources.length > 0) {
    const ctx = solcOutputSources[0].context!;
    for (const node of ctx.nodes) {
      if (node.type === 'StructDefinition') {
        const structDefinition = node as StructDefinition;
        solidityData.typeObjects[structDefinition.id] = {
          type: UserDefinedTypeKind.STRUCT,
          name: structDefinition.name!,
          id: structDefinition.id,
          bytes: userTypeDefinitionToBytes(structDefinition),
          subtypes: getSubTypes(node),
          vars: getStructVarData(structDefinition),
        };
      }
      if (node.type === 'EnumDefinition') {
        const enumDefinition = node as EnumDefinition;
        const values: {
          [valueName: string]: number;
        } = {};
        enumDefinition.vMembers.forEach((member, i) => {
          values[member.name!] = i;
        });
        solidityData.typeObjects[enumDefinition.id] = {
          type: UserDefinedTypeKind.ENUM,
          name: enumDefinition.name!,
          id: enumDefinition.id,
          bytes: userTypeDefinitionToBytes(enumDefinition),
          values,
        };
      }
    }
  }

  return solidityData;
}

function getSolidityData(solcOutput: any): ParsedSolidityData {
  const reader = new ASTReader();
  const sourceUnits = reader.read(solcOutput);
  return getSolidityDataFromSourceUnits(sourceUnits);
}

export { getSolidityData };
