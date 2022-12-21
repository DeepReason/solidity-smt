#!/usr/bin/env node
import { Command } from 'commander';
import { getSolidityData } from './src/sol_parsing/parse_solidity';
import { solidityDataToZ3Generators } from './src/translate/solidityZ3Generator';
import { textToZ3 } from './src/translate/toZ3';
import makeZ3 from './src/z3/z3';
import { repr_of_expr } from './src/z3/repr';

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

    const generators = solidityDataToZ3Generators(parsed_solidity, contract);
    const z3 = await makeZ3();
    const expr = textToZ3(input, z3, generators);
    console.log(
      JSON.stringify({
        expr: repr_of_expr(expr),
      }),
    );
  } catch (e) {
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
