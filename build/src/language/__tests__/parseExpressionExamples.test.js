import { parseExpression } from '../parseExpression.js';
describe('Test parsing of specific expressions', () => {
    it('Test 1', async () => {
        expect(parseExpression('// Comments should be ignored\n' +
            'msg.sender.balance@after + address(vault).balance@after <=\n' +
            'address(vault).balance@before + msg.sender.balance@before').hasError).toEqual(false);
    });
    it('Test 2', async () => {
        expect(parseExpression('// balance[...] refers to the storage variable while {ADDRESS}.balance refers to\n' +
            '// the ethereum balance of the address\n' +
            'balance[msg.sender]@after + address(vault).balance@before <=\n' +
            '    address(vault).balance@after + balance[msg.sender]@before').hasError).toEqual(false);
    });
    it('Test 3', async () => {
        expect(parseExpression('// By default, {ADDRESS}.balance is uint256\n' +
            '// To get signed comparison, we need users to cast\n' +
            'int256(msg.sender.balance@after) - int256(msg.sender.balance@before) <=\n' +
            '    int256(address(vault).balance@before) - int256(address(vault).balance@after)').hasError).toEqual(false);
    });
    it('Test 4', async () => {
        const parsedExpr = parseExpression('// We actually will also want something like this\n' +
            '// ForAll([{QUANTIFIER_DECLARATIONS}], {EXPRESSION})\n' +
            'ForAll(\n' +
            '    [address _sender],\n' +
            '    balance[_sender]@after + address(vault).balance@before <=\n' +
            '        address(vault).balance@after + balance[_sender]@before\n' +
            ')');
        expect(parsedExpr.hasError).toEqual(false);
    });
    it('Test 5', async () => {
        expect(parseExpression(`balance[msg.sender]@before >= address(vault).balance@before`).hasError).toEqual(false);
    });
    it('Test 6', async () => {
        expect(parseExpression('ForAll(\n' +
            '    [address read_idx],\n' +
            '    balance[read_idx]@after ==\n' +
            '        balance[read_idx]@before ||\n' +
            '    read_idx == msg.sender\n' +
            ') &&\n' +
            '(balance[msg.sender] + msg.sender.balance)@before >= (balance[msg.sender] + msg.sender.balance)@after &&\n' +
            '(msg.sender.balance + address(vault).balance)@after <= (msg.sender.balance + address(vault).balance)@before &&\n' +
            '(int256(balance[msg.sender]) - int256(address(vault).balance))@after <=\n' +
            '    (int256(balance[msg.sender]) - int256(address(vault).balance))@before').hasError).toEqual(false);
    });
    it('Test 7', async () => {
        expect(parseExpression('// This makes sense only explicitly in the context of the withdraw function\n' +
            'balance[msg.sender]@before >= amt &&\n' +
            'address(vault).balance@before >= amt &&\n' +
            'balance[msg.sender]@after <= balance[msg.sender]@before - amt &&\n' +
            'msg.sender.balance@after <= msg.sender.balance@before + amt &&\n' +
            'address(vault).balance@after >= address(vault).balance@before - amt').hasError).toEqual(false);
    });
    it('Test 8', async () => {
        expect(parseExpression("// This example doesn't use any temporal tags\n" +
            'ForAll(\n' +
            '    [address idx],\n' +
            '    balance[idx] <= address(vault).balance\n' +
            ')').hasError).toEqual(false);
    });
});
