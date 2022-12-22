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
  baseType: SolidityVarType;
  length: any;
};
export type MappingVarType = {
  type: VarTypeKind.Mapping;
  keyType: ElementaryVarType;
  valueType: SolidityVarType;
};

export type SolidityVarType = ElementaryVarType | MappingVarType | ArrayVarType | UserDefinedVarType;

export type StructVarData = {
  name: string;
  typeString: string;
  type: SolidityVarType;
  bytes: number;
  slot: SlotInfo;
  id: number;
};

export type ContractVarData = StructVarData & {
  mutability: Mutability;
};

export enum UserDefinedTypeKind {
  CONTRACT = 'Contract',
  STRUCT = 'Struct',
  ENUM = 'Enum',
}

export type ContractTypeObject = {
  id: number;
  type: UserDefinedTypeKind;
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
  type: UserDefinedTypeKind.STRUCT;
  name: string;
  subtypes: {
    [typeName: string]: number;
  };
  bytes: number;
  vars: {
    [varName: string]: StructVarData;
  };
};

export type EnumTypeObject = {
  id: number;
  type: UserDefinedTypeKind.ENUM;
  name: string;
  bytes: number;
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
