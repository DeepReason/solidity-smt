#!/usr/bin/env node
import { Command } from 'commander';
import { getSolidityData } from './src/sol_parsing';
import { translateToZ3 } from './src/translate';
import { dumps_expr } from './src/z3';
import fs from 'fs';

const program = new Command();

function create_generators(options: any) {
  if (options.solcOutput === undefined && options.solcOutputFile === undefined) {
    console.log(
      JSON.stringify({
        error: 'Must provide SOLC Output using --solc-output or --solc-output-file',
      }),
    );
    return;
  }

  let res = '';
  try {
    const solcOutput = JSON.parse(options.solcOutput ? options.solcOutput : fs.readFileSync(options.solcOutputFile));
    const solidityData = getSolidityData(solcOutput);
    res = JSON.stringify(solidityData);
  } catch (e) {
    res = JSON.stringify({
      error: '' + e,
    });
  }
  if (options.out !== undefined) {
    fs.writeFileSync(options.out, res);
  } else {
    console.log(res);
  }
}

async function translate(options: any) {
  try {
    const contract = options.contract;
    const input = options.input;
    const parsedSolidity = JSON.parse(options.parsedSolidity);
    const exposedImmutablesJSON = JSON.parse(options.exposedImmutables);
    const result = await translateToZ3(input, contract, parsedSolidity, exposedImmutablesJSON);
    if (!('error' in result)) {
      console.log(
        JSON.stringify({
          expr: dumps_expr(result.expr),
          warnings: result.warnings,
        }),
      );
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
  .option('-f, --solc-output-file <input_file>', 'Input File with JSON')
  .option('-o, --out <input_file>', 'Output file')
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
