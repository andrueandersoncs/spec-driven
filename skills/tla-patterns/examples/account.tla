---------------------------- MODULE account ----------------------------
\* Example: Banking Account State Machine
\* Demonstrates TLA+ patterns for spec-driven development
\*
\* Resources:
\* - TLA+ Repository: https://github.com/tlaplus/tlaplus
\* - TLA+ Examples: https://github.com/tlaplus/Examples
\* - TLA+ Cheatsheet: https://lamport.azurewebsites.net/tla/summary-standalone.pdf

EXTENDS Integers, Sequences

\* State variables
VARIABLES
    balance,        \* Current account balance
    transactions,   \* History of transactions
    state          \* Account state (active, frozen, closed)

\* Constants for model checking bounds
CONSTANTS
    MaxBalance,     \* Maximum balance to check
    MaxTransactions \* Maximum transaction history length

\* Type invariant
TypeOK ==
    /\ balance \in Int
    /\ balance >= -100  \* Allow small overdraft
    /\ balance <= MaxBalance
    /\ transactions \in Seq([type: {"deposit", "withdraw"}, amount: Nat, success: BOOLEAN])
    /\ Len(transactions) <= MaxTransactions
    /\ state \in {"active", "frozen", "closed"}

\* Initial state
Init ==
    /\ balance = 0
    /\ transactions = <<>>
    /\ state = "active"

\* Deposit action
Deposit(amount) ==
    /\ state = "active"
    /\ amount > 0
    /\ balance + amount <= MaxBalance
    /\ balance' = balance + amount
    /\ transactions' = Append(transactions,
         [type |-> "deposit", amount |-> amount, success |-> TRUE])
    /\ UNCHANGED state

\* Withdraw action (can fail if insufficient funds)
Withdraw(amount) ==
    /\ state = "active"
    /\ amount > 0
    /\ IF amount <= balance + 100  \* Allow overdraft up to 100
       THEN /\ balance' = balance - amount
            /\ transactions' = Append(transactions,
                 [type |-> "withdraw", amount |-> amount, success |-> TRUE])
       ELSE /\ UNCHANGED balance
            /\ transactions' = Append(transactions,
                 [type |-> "withdraw", amount |-> amount, success |-> FALSE])
    /\ UNCHANGED state

\* Freeze account
Freeze ==
    /\ state = "active"
    /\ state' = "frozen"
    /\ UNCHANGED <<balance, transactions>>

\* Unfreeze account
Unfreeze ==
    /\ state = "frozen"
    /\ state' = "active"
    /\ UNCHANGED <<balance, transactions>>

\* Close account (only if balance is zero)
Close ==
    /\ state \in {"active", "frozen"}
    /\ balance = 0
    /\ state' = "closed"
    /\ UNCHANGED <<balance, transactions>>

\* Next state relation
Next ==
    \/ \E a \in 1..100: Deposit(a)
    \/ \E a \in 1..100: Withdraw(a)
    \/ Freeze
    \/ Unfreeze
    \/ Close

\* Fairness - ensure progress
Fairness ==
    /\ WF_<<balance, transactions, state>>(Next)

\* Complete specification
vars == <<balance, transactions, state>>
Spec == Init /\ [][Next]_vars /\ Fairness

\*===========================================================================
\* SAFETY PROPERTIES
\*===========================================================================

\* Balance never goes below overdraft limit
BalanceWithinLimits == balance >= -100

\* Closed account has zero balance
ClosedAccountZeroBalance == state = "closed" => balance = 0

\* Can only withdraw from active account
WithdrawOnlyWhenActive ==
    [][(\E a \in 1..100: Withdraw(a)) => state = "active"]_vars

\*===========================================================================
\* LIVENESS PROPERTIES
\*===========================================================================

\* If account is frozen, it can eventually be unfrozen or closed
FrozenEventuallyResolved ==
    state = "frozen" ~> (state = "active" \/ state = "closed")

\* Successful deposits eventually reflected
DepositEventuallyReflected ==
    \A a \in 1..100:
        (Deposit(a) /\ balance' = balance + a) ~> balance >= a

==========================================================================
