pragma solidity ^0.8.0;

contract VaultBasic {

    uint private x;
    uint64 private y;
    address private z;
    mapping(address => uint256) public balance;

    function deposit() public payable {
        balance[msg.sender] += msg.value;
    }

    function withdraw(uint256 amt) public {
        require(balance[msg.sender] >= amt);
        balance[msg.sender] -= amt;
        (bool success, ) = msg.sender.call{value: amt}("");
        if (!success) {
            balance[msg.sender] += amt;
        }
    }
}