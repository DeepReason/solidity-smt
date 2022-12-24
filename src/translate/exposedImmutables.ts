import { loads_expr, Z3Obj } from '../z3';
import { Expr } from 'z3-solver';

export type Serialized<T> = {
  [Key in keyof T]: T[Key] extends Expr ? string : T[Key] extends object ? Serialized<T[Key]> : T[Key];
};

export type GraphDeployments = {
  main: {
    address: Expr;
    expanded: Expr;
  };
  deployments: {
    [contractName: string]: {
      address: Expr;
      expanded: Expr;
    }[];
  };
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
    [graphContract: string]: GraphDeployments;
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
  const d: {
    [graphName: string]: GraphDeployments;
  } = {};
  for (const [graphContract, graphDeployInfo] of Object.entries(exposedImmutablesJSON.deploymentAddresses)) {
    const graphDeploys: {
      [contractName: string]: {
        address: Expr;
        expanded: Expr;
      }[];
    } = {};
    for (const [contractName, contractDeploys] of Object.entries(graphDeployInfo.deployments)) {
      graphDeploys[contractName] = contractDeploys.map(contractDeploy => ({
        address: exprs[contractDeploy.address],
        expanded: exprs[contractDeploy.expanded],
      }));
    }
    d[graphContract] = {
      main: {
        address: exprs[graphDeployInfo.main.address],
        expanded: exprs[graphDeployInfo.main.expanded],
      },
      deployments: graphDeploys,
    };
  }
  res.deploymentAddresses = d;
  return res;
}
