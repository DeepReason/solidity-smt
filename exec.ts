#!/usr/bin/env node
import { Command } from 'commander';
import { getSolidityData } from './src/sol_parsing';
import { translateFromParsedSolidity } from './src/translate';
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
    const parsed_solidity = JSON.parse(options.parsedSolidity);
    const result = await translateFromParsedSolidity(input, contract, parsed_solidity);
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
  .description('Translate Solidity SMT')
  .action(translate);

program.parse();
