'''
Problem Statement:
------------------
Design and verify a multi-signature authorization mechanism for a critical administrative function (e.g., a contract upgrade).
The system must ensure that the function can only be executed when a minimum threshold of distinct administrator approvals is met.
Specifically, the verification task is to prove that if fewer than the required number of administrators have approved the action,
then the critical function will not execute.

Solidity Code Sketch:
---------------------
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract MultiSigAdmin {
    bool public critical_upgrade;
    address[] public admins;
    mapping(address => bool) public isAdmin;
    uint public constant REQUIRED_SIGNATURES = 3;

    // Mapping from a transaction hash to the number of approvals
    mapping(bytes32 => uint) public approvals;
    // Mapping to track if an admin has approved a specific transaction
    mapping(bytes32 => mapping(address => bool)) public approvedBy;

    constructor(address[] memory _admins) {
        require(_admins.length >= REQUIRED_SIGNATURES, "Not enough admins");
        admins = _admins;
        for (uint i = 0; i < _admins.length; i++) {
            isAdmin[_admins[i]] = true;
        }
        critical_upgrade = false;
    }

    // Function to approve a critical action, e.g., a contract upgrade
    function approveAction(address target) external {
        require(isAdmin[msg.sender], "Caller is not an admin");
        bytes32 txHash = keccak256(abi.encode(target));
        require(!approvedBy[txHash][msg.sender], "Admin already approved");
        approvedBy[txHash][msg.sender] = true;
        approvals[txHash] += 1;
    }

    // Critical function that should only execute if enough approvals are collected
    function upgradeContract(address newContract) external {
        bytes32 txHash = keccak256(abi.encode(newContract));
        require(approvals[txHash] >= REQUIRED_SIGNATURES, "Not enough approvals");
        // Critical upgrade logic goes here
        critcal_update = true;

    }
}

Proof Problem:
--------------
Prove that the 'upgradeContract' function cannot be executed unless at least three distinct administrator approvals are obtained.
Formally, show that for any execution trace, if the precondition

    approvals[keccak256(abi.encode(newContract))] >= REQUIRED_SIGNATURES

does not hold, then the function body is never reached. This verifies that if fewer than three admins have approved, 
the call to 'upgradeContract' will always revert.
'''

from z3 import *

num_admins = 10 # assume there are 10 admins

# example: approvals [target] = 10
approvals = Array("approvals", BitVecSort (160), IntSort()) 
updated_approvals = Array("updated_approvals", BitVecSort (160), IntSort()) 
# example: isAdmin [target] = true/false
isAdmin = Array("isAdmin", BitVecSort (160), BoolSort ()) 
updated_isAdmin = Array("updated_isAdmin", BitVecSort (160), BoolSort ()) 

# example: approvedBy[target][msg.sender] = true/false
approvedBy = Array("approvedBy", BitVecSort(160), ArraySort(BitVecSort(160), BoolSort()))  
updated_approvedBy = Array("updated_approvedBy", BitVecSort(160), ArraySort(BitVecSort(160), BoolSort()))  

admins = Array ("admins", IntSort (), BitVecSort (160))
sender = BitVec("sender", 160)
target = BitVec ("target", 160)

critical_upgrade = Bool ("critical_upgrade")
updated_critical_upgrade = Bool ("critical_upgrade")
REQUIRED_SIGNATURES = Int ('REQUIRED_SIGNATURES')

s = Solver ()

# constructor modeling

s.add (REQUIRED_SIGNATURES == 3)

for i in range (0, num_admins):
    admin = BitVec(f'admin_{i}', 160)
    admins = Store (admins, i, admin)
    isAdmin = Store (isAdmin, admin, True)

s.add (critical_upgrade == False)

# approveAction modeling

require1 = (isAdmin [sender] == True)
require2 = (approvedBy [target][sender] == False)

action1 = (updated_approvedBy [target][sender]==Not (approvedBy [target][sender]))
action2 =  (updated_approvals [target] == approvals [target] + 1) 

s.add (Implies (And (require1, require2), And (action1, action2)))
s.add (Implies (updated_approvals [target] < REQUIRED_SIGNATURES, updated_critical_upgrade==critical_upgrade))
s.add (updated_approvals [target] >= REQUIRED_SIGNATURES, updated_critical_upgrade == Not (critical_upgrade))

'''
the following constraint asserts that there is a state where, 
despite having insufficient approvals, 
the critical upgrade flag is set to True (in the critical upgrade section). 
In a correctly implemented 
contract, no such state should exist, so the solver should return unsat. 
This unsat result would prove that if fewer than three signatures 
are present, then the upgrade functions body (which sets the upgrade flag) 
is never reached. 
'''
s.add(And(updated_approvals[target] < REQUIRED_SIGNATURES, updated_critical_upgrade == True))


if s.check () == sat:
    print ("Critical upgrade possible without enough signer. Counter Example Found! ",s.model())
else:
    print ("Critical upgrade NOT possible without enough signer.")








