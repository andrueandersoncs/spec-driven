// Example: Banking Account with Formal Contracts
// Demonstrates Dafny patterns for spec-driven development

module AccountExample {

  // Refinement type: non-negative balance
  type Balance = x: int | x >= 0

  // Refinement type: positive amount
  type PositiveAmount = x: int | x > 0

  // Main entity class with invariants
  class Account {
    var balance: int
    var owner: string

    // Class invariant: balance never negative
    invariant balance >= 0

    // Constructor with precondition
    constructor(initialBalance: int, ownerName: string)
      requires initialBalance >= 0
      requires |ownerName| > 0
      ensures balance == initialBalance
      ensures owner == ownerName
    {
      balance := initialBalance;
      owner := ownerName;
    }

    // Deposit method with contract
    method Deposit(amount: int)
      requires amount > 0
      ensures balance == old(balance) + amount
      modifies this
    {
      balance := balance + amount;
    }

    // Withdraw method with rich contract
    method Withdraw(amount: int) returns (success: bool)
      requires amount > 0
      ensures success ==> balance == old(balance) - amount
      ensures !success ==> balance == old(balance)
      ensures success ==> amount <= old(balance)
      modifies this
    {
      if amount <= balance {
        balance := balance - amount;
        success := true;
      } else {
        success := false;
      }
    }

    // Transfer between accounts
    method Transfer(other: Account, amount: int) returns (success: bool)
      requires amount > 0
      requires other != this
      ensures success ==> balance == old(balance) - amount
      ensures success ==> other.balance == old(other.balance) + amount
      ensures !success ==> balance == old(balance)
      ensures !success ==> other.balance == old(other.balance)
      modifies this, other
    {
      if amount <= balance {
        balance := balance - amount;
        other.balance := other.balance + amount;
        success := true;
      } else {
        success := false;
      }
    }

    // Query method (no modification)
    function GetBalance(): int
      reads this
    {
      balance
    }
  }

  // Predicate for validation
  predicate ValidAccountName(name: string) {
    |name| > 0 && |name| <= 100
  }

  // Ghost function for specification
  ghost predicate AccountsConsistent(a1: Account, a2: Account)
    reads a1, a2
  {
    a1.balance >= 0 && a2.balance >= 0
  }
}
