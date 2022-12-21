import fs from 'fs';
import path from 'path';
import { getSolidityData } from '../parse_solidity.js';
describe('Try creating generators', () => {
    it('VaultBasic + Spec', async () => {
        // Read examples/solc_output.json
        const solcOutput = JSON.parse(fs.readFileSync(path.join(__dirname, 'examples/solc_output.json'), 'utf8'));
        const solidityData = getSolidityData(solcOutput);
        // Check against examples/expected_output.json
        const expectedOutput = JSON.parse(fs.readFileSync(path.join(__dirname, 'examples/expected_output.json'), 'utf8'));
        expect(solidityData).toEqual(expectedOutput);
    });
});
