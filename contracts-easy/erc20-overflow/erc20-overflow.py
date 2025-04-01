'''
> **🧾 Problem Statement: Ensuring Safe Token Withdrawals by Preventing Arithmetic Underflow**
>
> ```solidity
> function withdraw(uint amount) public {
>     require(address(msg.sender).balance >= amount, "Not enough funds");
>     (bool sent, ) = msg.sender.call{value: amount}("");
>     msg.sender.balance = msg.sender.balance - amount;
>     require(sent, "Failed to send Ether");
> }
> ```
>
> This implementation is problematic for two key reasons:
>
> 1. **Incorrect Balance Modification:** The statement `msg.sender.balance = msg.sender.balance - amount;` is semantically invalid in Solidity, as the `balance` field is a read-only property managed by the Ethereum Virtual Machine (EVM). This line does not compile in practice.
>
> 2. **Potential Arithmetic Underflow:** Assuming the intention is to maintain an internal balance ledger (e.g., `mapping(address => uint) balances;`), subtracting `amount` from a user's balance without a prior bounds check can result in an arithmetic underflow. In Solidity versions prior to 0.8.0, such underflows would silently wrap around, leading to critical security vulnerabilities. Even in Solidity 0.8.0 and beyond, where underflows trigger a runtime exception, verifying that this condition is unreachable under correct usage remains essential.
>
> **Formal Verification Goal:** Prove that if the withdrawal function is guarded by a check ensuring that `balances[msg.sender] ≥ amount`, then the subsequent subtraction `balances[msg.sender] - amount` is safe and cannot cause an underflow.
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



