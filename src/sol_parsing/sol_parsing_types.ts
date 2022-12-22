import { Mutability } from 'solc-typed-ast/dist/ast/constants';

export type SlotInfo = {
  slot: [number, number];
  intraSlot: [number, number] | undefined;
};

export enum VarTypeKind {
  Mapping,
  ArrayTypeName,
  ElementaryTypeName,
  UserDefinedTypeName,
}

export type ElementaryVarType = {
  type: VarTypeKind.ElementaryTypeName;
  name: string;
  stateMutability: string | null;
};
export type UserDefinedVarType = {
  type: VarTypeKind.UserDefinedTypeName;
  name: string;
};
export type ArrayVarType = {
  type: VarTypeKind.ArrayTypeName;
  baseType: VarType;
  length: any;
};
export type MappingVarType = {
  type: VarTypeKind.Mapping;
  keyType: ElementaryVarType | UserDefinedVarType;
  valueType: VarType;
};
export type VarType = ElementaryVarType | MappingVarType | ArrayVarType | UserDefinedVarType;
export type ContractVarData = {
  name: string;
  typeString: string;
  type: VarType;
  bytes: number;
  id: number;
  slot: SlotInfo;
  mutability: Mutability;
};
export type StructVarData = {
  name: string;
  typeString: string;
  type: VarType;
  bytes: number;
  slot: SlotInfo;
  id: number;
};
export type ContractTypeObject = {
  id: number;
  type: 'Contract';
  sourceUnit: string;
  name: string;
  subtypes: {
    [typeName: string]: number;
  };
  vars: {
    [varName: string]: ContractVarData;
  };
};
export type StructTypeObject = {
  id: number;
  type: 'Struct';
  name: string;
  subtypes: {
    [typeName: string]: number;
  };
  vars: {
    [varName: string]: StructVarData;
  };
};
export type EnumTypeObject = {
  id: number;
  type: 'Enum';
  name: string;
  values: {
    [valueName: string]: number;
  };
};
export type TypeObject = ContractTypeObject | StructTypeObject | EnumTypeObject;
export type ParsedSolidityData = {
  contractId: {
    [contractName: string]: number;
  };
  sourceUnits: {
    [absolutePath: string]: {
      contracts: number[];
      types: {
        [typeName: string]: number;
      };
    };
  };
  typeObjects: {
    [typeId: number]: TypeObject;
  };
};
