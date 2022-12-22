pragma solidity ^0.8.0;

contract VaultBasic {

    struct TestStruct {
        uint32 a;
        uint32 b;
    }

    enum TestEnum {
        A,
        B,
        C
    }

    uint x;
    uint64 y;
    address z;
    mapping(address => uint256) public balance;
    mapping(uint256 => uint) public test;
    TestStruct public testStruct;
    uint8 public immutable t;

    constructor() {
        t = 5;
    }

    function deposit() public payable {
        balance[msg.sender] += msg.value;
    }

    function withdraw(uint256 amt) public {
        require(balance[msg.sender] >= amt);
        balance[msg.sender] -= amt;
        (bool success,) = msg.sender.call{value : amt}("");
        if (!success) {
            balance[msg.sender] += amt;
        }
    }

}