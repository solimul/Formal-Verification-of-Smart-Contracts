'''
Problem Statement: Verifying Arithmetic Safety in Token Withdrawals

Given the following function:

    mapping(address => uint) public balances;

    function withdraw(uint amount) public {
        require(address(this).balance >= amount, "Not enough funds");
        (bool sent, ) = msg.sender.call{value: amount}("");
        balances[address(this)] = balances[address(this)] - amount;
        require(sent, "Failed to send Ether");
    }

Verification Goal:

Prove that the subtraction operation:

    balances[address(this)] - amount

does not cause an arithmetic underflow at runtime, assuming the function is invoked under the guard:

    address(this).balance ≥ amount

This requires showing that under this guard, the expression `balances[address(this)] - amount` evaluates safely within the valid range of unsigned 256-bit integers (i.e., without wrapping around or reverting due to underflow).
''' 

from z3 import *

user_balance = BitVec ('user_balance',256)
updated_user_balance = BitVec ('updated_user_balance',256)
requested_amount = BitVec ('requested_amount',256)

s = Solver ()

'''
In unsigned 256-bit arithmetic (`uint256`), underflow occurs when a larger value is subtracted
from a smaller one. Since negative numbers are not representable, the result wraps around
using modular arithmetic (mod 2^256).

Example:

    uint256 x = 5;
    uint256 y = 10;
    uint256 z = x - y;

Since 5 - 10 = -5 is invalid in `uint256`, it wraps around to:

    z = 2^256 - 5 = 115792089237316195423570985008687907853269984665640564039457584007913129639931

This value is syntactically valid but semantically incorrect in contexts like balance updates,
where such a subtraction would indicate a logic error.

To prevent underflow, the subtraction must be guarded with:

    UGT(user_balance, requested_amount)

This ensures that `user_balance > requested_amount` before computing:

    updated_user_balance = user_balance - requested_amount

To formally verify that underflow cannot occur under this guard, we introduce the constraint:

    UGT(updated_user_balance, user_balance)

This condition would only hold if underflow occurred and the result wrapped around to a large value.
Therefore, the conjunction of all three constraints:

    - UGT(user_balance, requested_amount)
    - updated_user_balance == user_balance - requested_amount
    - UGT(updated_user_balance, user_balance)

should be unsatisfiable. If Z3 returns `unsat`, it proves that underflow is impossible given the guard.
'''



#s.add (UGT (requested_amount,BitVecVal (0, 256)))

s.add (
        And (
                UGT (user_balance, requested_amount), 
                updated_user_balance == user_balance - requested_amount, 
                UGT(updated_user_balance, user_balance)            
            ) 
    )

if s.check() == sat:
    print ("Counter Example Found: ", s.model ())
else:
    print ("Underflow of the User Balance never happens")



