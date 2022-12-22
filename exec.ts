#!/usr/bin/env node
import { Command } from 'commander';
import { getSolidityData } from './src/sol_parsing';
import { translateToZ3 } from './src/translate';
import { dumps_expr } from './src/z3';

const program = new Command();

function create_generators(options: any) {
  if (options.solcOutput === undefined) {
    console.log(
      JSON.stringify({
        error: 'Must provide SOLC Output using --solc-output',
      }),
    );
    return;
  }
  try {
    const solcOutput = JSON.parse(options.solcOutput);
    const solidityData = getSolidityData(solcOutput);
    console.log(JSON.stringify(solidityData));
  } catch (e) {
    console.log(
      JSON.stringify({
        error: '' + e,
      }),
    );
  }
}

async function translate(options: any) {
  try {
    const contract = options.contract;
    const input = options.input;
    const parsedSolidity = JSON.parse(options.parsedSolidity);
    const exposedImmutablesJSON = JSON.parse(options.exposedImmutables);
    const result = await translateToZ3(input, contract, parsedSolidity, exposedImmutablesJSON);
    if (result.error === undefined) {
      result.expr = dumps_expr(result.expr);
      console.log(JSON.stringify(result));
    }
  } catch (e) {
    console.error(e);
    console.log(
      JSON.stringify({
        error: '' + e,
      }),
    );
  }
}

program
  .command('parse')
  .option('-s, --solc-output <input>', 'Input JSON')
  .description('Parse SOLC Output')
  .action(create_generators);

program
  .command('translate')
  .option('-c, --contract <contract>', 'Contract Name')
  .option('-i, --input <input>', 'Input Text')
  .option(
    '-s, --parsed-solidity <parsed_solidity>',
    'Parsed SOLC Output (Generate using the `solidity-smt parse` command)',
  )
  .option(
    '-e, --exposed-immutables <exposed_immutables>',
    'Exposed Immutables (Generated from the DeepReason analysis)',
  )
  .description('Translate Solidity SMT')
  .action(translate);

program.parse();
