import fs from 'fs';
import path from 'path';
import { getSolidityData } from '../parse_solidity';

describe('Try creating generators', () => {
  it('VaultBasic + Spec', async () => {
    // Read examples/VaultBasic_solc_output.json
    const solcOutput = JSON.parse(
      fs.readFileSync(path.join(__dirname, 'examples/VaultBasic_solc_output.json'), 'utf8'),
    );
    expect(() => getSolidityData(solcOutput)).not.toThrow();
  });

  it('Popcorn', async () => {
    // Read examples/Popcorn_solc_output.json
    const solcOutput = JSON.parse(fs.readFileSync(path.join(__dirname, 'examples/Popcorn_solc_output.json'), 'utf8'));
    expect(() => getSolidityData(solcOutput)).not.toThrow();

    const solidityData = getSolidityData(solcOutput);
  });
});
