import { loads_expr, Z3Obj } from '../z3';
import { Expr } from 'z3-solver';

export type ExposedImmutables = {
  exposedImmutables: {
    [contractName: string]: {
      [varName: string]: {
        [addressHash: string]: Expr;
      };
    };
  };
  deploymentAddresses: {
    [contractName: string]: Expr;
  };
};

export function loadExposedImmutables(z3: Z3Obj, exposedImmutablesJSON: any): ExposedImmutables {
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
    Object.entries(exposedImmutablesJSON.exposedImmutables).map(([contractName, contractImmutables]) => [
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
  );
  res.deploymentAddresses = Object.fromEntries(
    Object.entries(exposedImmutablesJSON.deploymentAddresses).map(([k, v]) => {
      return [k, exprs[v as number]];
    }),
  );
  return res;
}
