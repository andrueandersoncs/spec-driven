// Example: Banking Account with Formal Contracts
// Demonstrates Dafny patterns for spec-driven development
// See: https://dafny.org/latest/DafnyRef/DafnyRef

module AccountExample {

  // Refinement type: non-negative balance
  // Subset types constrain base types with predicates
  // See: https://dafny.org/latest/DafnyRef/DafnyRef#sec-subset-types
  type Balance = x: int | x >= 0 witness 0

  // Refinement type: positive amount
  type PositiveAmount = x: int | x > 0 witness 1

  // Main entity class
  // Dafny uses Valid() predicates for class invariants (dynamic frames pattern)
  // See: https://dafny.org/latest/DafnyRef/DafnyRef#sec-class-types
  class Account {
    var balance: int
    var owner: string

    // Object invariant expressed as a Valid() predicate
    // This is the standard Dafny idiom for class invariants
    ghost predicate Valid()
      reads this
    {
      balance >= 0 && |owner| > 0
    }

    // Constructor establishes the object invariant
    constructor(initialBalance: int, ownerName: string)
      requires initialBalance >= 0
      requires |ownerName| > 0
      ensures Valid()
      ensures balance == initialBalance
      ensures owner == ownerName
    {
      balance := initialBalance;
      owner := ownerName;
    }

    // Deposit method with contract
    // Requires Valid() as precondition, ensures Valid() as postcondition
    method Deposit(amount: int)
      requires Valid()
      requires amount > 0
      modifies this
      ensures Valid()
      ensures balance == old(balance) + amount
      ensures owner == old(owner)
    {
      balance := balance + amount;
    }

    // Withdraw method with rich contract
    method Withdraw(amount: int) returns (success: bool)
      requires Valid()
      requires amount > 0
      modifies this
      ensures Valid()
      ensures success ==> balance == old(balance) - amount
      ensures !success ==> balance == old(balance)
      ensures success ==> amount <= old(balance)
      ensures owner == old(owner)
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
      requires Valid() && other.Valid()
      requires amount > 0
      requires other != this
      modifies this, other
      ensures Valid() && other.Valid()
      ensures success ==> balance == old(balance) - amount
      ensures success ==> other.balance == old(other.balance) + amount
      ensures !success ==> balance == old(balance)
      ensures !success ==> other.balance == old(other.balance)
      ensures owner == old(owner) && other.owner == old(other.owner)
    {
      if amount <= balance {
        balance := balance - amount;
        other.balance := other.balance + amount;
        success := true;
      } else {
        success := false;
      }
    }

    // Query function (no modification)
    // See: https://dafny.org/latest/DafnyRef/DafnyRef#sec-function-declaration
    function GetBalance(): int
      reads this
    {
      balance
    }
  }

  // Predicate for validation
  // See: https://dafny.org/latest/DafnyRef/DafnyRef#642-predicates
  predicate ValidAccountName(name: string) {
    |name| > 0 && |name| <= 100
  }

  // Ghost predicate for specification-only use
  ghost predicate AccountsConsistent(a1: Account, a2: Account)
    reads a1, a2
  {
    a1.Valid() && a2.Valid()
  }
}
