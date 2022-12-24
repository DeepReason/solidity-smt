import { loads_expr, Z3Obj } from '../z3';
import { Expr } from 'z3-solver';
import { AnySort, SortToExprMap } from '../../z3/src/api/js/src/high-level';

export type Serialized<T> = {
  [Key in keyof T]: T[Key] extends Expr ? string : T[Key] extends object ? Serialized<T[Key]> : T[Key];
};

export type ExposedImmutables = {
  exposedImmutables: {
    [deployContract: string]: {
      [contractName: string]: {
        [varName: string]: {
          [addressHash: string]: Expr;
        };
      };
    };
  };
  deploymentAddresses: {
    [graphContract: string]: {
      [contractName: string]: {
        address: Expr;
        expanded: Expr;
      };
    };
  };
};

export type SerializedExposedImmutables = Serialized<ExposedImmutables> & {
  exprs: {
    [exprHash: string]: string;
  };
};

export function loadExposedImmutables(
  z3: Z3Obj,
  exposedImmutablesJSON: SerializedExposedImmutables,
): ExposedImmutables {
  const res: ExposedImmutables = {
    exposedImmutables: {},
    deploymentAddresses: {},
  };

  const exprs: {
    [exprHash: string]: Expr;
  } = {};
  for (const [exprHash, exprStr] of Object.entries(exposedImmutablesJSON.exprs)) {
    exprs[exprHash] = loads_expr(z3, exprStr as string) as Expr;
  }
  res.exposedImmutables = Object.fromEntries(
    Object.entries(exposedImmutablesJSON.exposedImmutables).map(([deployContract, deploymentImmutables]) => [
      deployContract,
      Object.fromEntries(
        Object.entries(deploymentImmutables as any).map(([contractName, contractImmutables]) => [
          contractName,
          Object.fromEntries(
            Object.entries(contractImmutables as any).map(([varName, varImmutables]) => [
              varName,
              Object.fromEntries(
                Object.entries(varImmutables as any).map(([addressHash, exprHash]) => [
                  addressHash,
                  exprs[exprHash as number],
                ]),
              ),
            ]),
          ),
        ]),
      ),
    ]),
  );
  res.deploymentAddresses = Object.fromEntries(
    Object.entries(exposedImmutablesJSON.deploymentAddresses).map(([graphContract, deployInfo]) => [
      graphContract,
      Object.fromEntries(
        Object.entries(deployInfo as any).map(([contractName, contractAddressInfo]) => [
          contractName,
          {
            address: exprs[(contractAddressInfo as any).address as number],
            expanded: exprs[(contractAddressInfo as any).expanded as number],
          },
        ]),
      ),
    ]),
  );
  return res;
}
