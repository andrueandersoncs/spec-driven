---
name: dafny-patterns
description: This skill should be used when writing Dafny specifications, creating refinement types, writing method contracts (requires/ensures), defining class invariants, working with Dafny verification, or when the user asks "write a Dafny spec", "create a contract", "define an invariant", "add preconditions", "add postconditions", "verify this with Dafny", "how do I write a Dafny class", "extract code from Dafny", or "compile Dafny to JavaScript".
version: 0.1.0
---

# Dafny Patterns

Write structural specifications using Dafny's verification-aware language.

## Core Concepts

Dafny models **structure**: what is true at any single point in time.

| Construct | Purpose | Verification |
|-----------|---------|--------------|
| Refinement types | Constrain data values | Compile-time + Z3 |
| Class invariants | Entity state constraints | Checked at boundaries |
| Preconditions (`requires`) | Operation input constraints | Caller responsibility |
| Postconditions (`ensures`) | Operation output guarantees | Implementer responsibility |
| Predicates | Reusable boolean conditions | Used in other constructs |

## File Organization

Organize Dafny specs in `specs/dafny/`:

```
specs/dafny/
├── structure.dfy      # Main types and entities
├── operations.dfy     # Methods and their contracts
├── predicates.dfy     # Reusable predicates
└── domains/           # Domain-specific modules
    ├── finance.dfy
    └── auth.dfy
```

## Refinement Types

Constrain primitive types with logical predicates. See [Subset Types](https://dafny.org/latest/DafnyRef/DafnyRef#sec-subset-types) in the Dafny Reference Manual.

### Pattern: Constrained Numeric

```dafny
// Natural language: "Age must be positive and under 150"
type Age = x: int | 0 < x < 150

// Natural language: "Price is non-negative"
type Price = x: real | x >= 0.0

// Natural language: "Quantity is positive"
type Quantity = x: int | x > 0
```

### Pattern: Constrained String

```dafny
// Non-empty strings
type NonEmptyString = s: string | |s| > 0

// Bounded length
type Username = s: string | 3 <= |s| <= 20
```

### Pattern: Subset Types

```dafny
// Natural language: "Only certain status values are valid"
datatype Status = Pending | Active | Completed | Cancelled

// Natural language: "Active statuses are Pending or Active"
type ActiveStatus = s: Status | s.Pending? || s.Active?
```

## Class Invariants

State constraints that hold between method calls. In Dafny, class invariants are expressed using `Valid()` predicates—the standard "dynamic frames" idiom. See [Class Types](https://dafny.org/latest/DafnyRef/DafnyRef#sec-class-types) in the Dafny Reference Manual.

**Note**: The `invariant` keyword is used for loop invariants, not class-level invariants. For object invariants, define a `Valid()` predicate and include it in method pre/postconditions.

### Pattern: Simple Invariant with Valid()

```dafny
class Account {
  var balance: int

  // Object invariant as a predicate
  // Natural language: "Balance never negative"
  ghost predicate Valid()
    reads this
  {
    balance >= 0
  }

  constructor(initial: int)
    requires initial >= 0
    ensures Valid()
    ensures balance == initial
  {
    balance := initial;
  }

  method Deposit(amount: int)
    requires Valid()
    requires amount > 0
    modifies this
    ensures Valid()
    ensures balance == old(balance) + amount
  {
    balance := balance + amount;
  }
}
```

### Pattern: Computed Invariant

```dafny
class ShoppingCart {
  var items: seq<CartItem>
  var total: real

  function SumPrices(xs: seq<CartItem>): real {
    if |xs| == 0 then 0.0
    else xs[0].price + SumPrices(xs[1..])
  }

  // Natural language: "Total equals sum of item prices"
  ghost predicate Valid()
    reads this
  {
    total == SumPrices(items)
  }

  method AddItem(item: CartItem)
    requires Valid()
    modifies this
    ensures Valid()
    ensures items == old(items) + [item]
  {
    items := items + [item];
    total := total + item.price;
  }
}
```

### Pattern: Relationship Invariant

```dafny
class Order {
  var customer: Customer
  var items: seq<OrderItem>

  // Natural language: "Order always has at least one item"
  // Natural language: "All items reference this order"
  ghost predicate Valid()
    reads this, items
  {
    |items| > 0 &&
    forall i :: 0 <= i < |items| ==> items[i].order == this
  }
}
```

## Method Contracts

Specify operation behavior with pre/postconditions. See [Method Specification](https://dafny.org/latest/DafnyRef/DafnyRef#sec-method-specification), [Requires Clause](https://dafny.org/latest/DafnyRef/DafnyRef#sec-requires-clause), and [Ensures Clause](https://dafny.org/latest/DafnyRef/DafnyRef#sec-ensures-clause) in the Dafny Reference Manual.

### Pattern: Basic Contract

```dafny
method Withdraw(amount: int) returns (success: bool)
  // Natural language: "Can only withdraw positive amount"
  requires amount > 0
  // Natural language: "Can only withdraw if sufficient funds"
  requires amount <= balance
  // Natural language: "Success means balance decreased by amount"
  ensures success ==> balance == old(balance) - amount
  // Natural language: "Failure means balance unchanged"
  ensures !success ==> balance == old(balance)
{
  balance := balance - amount;
  success := true;
}
```

### Pattern: Frame Conditions

```dafny
method UpdateEmail(newEmail: string)
  requires ValidEmail(newEmail)
  // What changes
  modifies this
  // What stays the same
  ensures name == old(name)
  ensures age == old(age)
  // What changes
  ensures email == newEmail
{
  email := newEmail;
}
```

### Pattern: Conditional Postcondition

```dafny
method FindUser(id: UserId) returns (user: User?)
  // Natural language: "Returns user if exists, null otherwise"
  ensures user != null ==> user.id == id
  ensures user == null ==> id !in knownUsers
```

## Predicates

Reusable boolean conditions. See [Predicates](https://dafny.org/latest/DafnyRef/DafnyRef#642-predicates) in the Dafny Reference Manual.

### Pattern: Validation Predicate

```dafny
// Natural language: "Email must contain @ and ."
predicate ValidEmail(s: string) {
  exists i, j :: 0 < i < j < |s| - 1 && s[i] == '@' && s[j] == '.'
}

// Natural language: "Password has minimum complexity"
predicate StrongPassword(s: string) {
  |s| >= 8 &&
  exists c :: c in s && IsUpperCase(c) &&
  exists c :: c in s && IsDigit(c)
}
```

### Pattern: Collection Predicate

```dafny
// Natural language: "All elements satisfy condition"
predicate AllPositive(xs: seq<int>) {
  forall i :: 0 <= i < |xs| ==> xs[i] > 0
}

// Natural language: "No duplicates in sequence"
predicate Unique<T>(xs: seq<T>) {
  forall i, j :: 0 <= i < j < |xs| ==> xs[i] != xs[j]
}
```

### Pattern: Relationship Predicate

```dafny
// Natural language: "Emails unique across users"
predicate UniqueEmails(users: set<User>) {
  forall u1, u2 :: u1 in users && u2 in users && u1 != u2
    ==> u1.email != u2.email
}
```

## Ghost State

Specification-only state for verification. Ghost variables exist only during verification and are erased at compile time.

### Pattern: Audit Trail

```dafny
class SecureResource {
  var data: string
  ghost var accessLog: seq<AccessEvent>  // Spec only

  method Access(user: User) returns (d: string)
    ensures accessLog == old(accessLog) + [AccessEvent(user, d)]
  {
    d := data;
    accessLog := accessLog + [AccessEvent(user, d)];
  }
}
```

## Verification Workflow

See [Verification](https://dafny.org/latest/DafnyRef/DafnyRef#sec-verification) in the Dafny Reference Manual for comprehensive guidance on debugging verification failures and performance issues.

### Running Verification

```bash
# Verify single file
dafny verify specs/dafny/structure.dfy

# Verify with timeout
dafny verify --verification-time-limit:60 specs/dafny/structure.dfy

# Verify all files
dafny verify specs/dafny/*.dfy
```

### Interpreting Results

| Result | Meaning | Action |
|--------|---------|--------|
| `Verified` | All proofs succeed | Specification is consistent |
| `Error: precondition might not hold` | Caller doesn't guarantee requires | Fix call site or weaken precondition |
| `Error: postcondition might not hold` | Implementation doesn't guarantee ensures | Fix implementation or weaken postcondition |
| `Error: invariant might not hold` | State constraint violated | Fix method or strengthen precondition |
| `Timeout` | Prover couldn't decide | Simplify or add hints |

### Common Verification Hints

```dafny
// Help prover with loop invariants
method Sum(xs: seq<int>) returns (s: int)
  ensures s == SumSpec(xs)
{
  s := 0;
  var i := 0;
  while i < |xs|
    invariant 0 <= i <= |xs|
    invariant s == SumSpec(xs[..i])
  {
    s := s + xs[i];
    i := i + 1;
  }
}
```

## Code Extraction

Dafny compiles to multiple targets. See [Compilation](https://dafny.org/latest/DafnyRef/DafnyRef#sec-compilation) in the Dafny Reference Manual for full details on each target language.

```bash
# To JavaScript (for TypeScript projects)
dafny build --target:js specs/dafny/structure.dfy -o generated/structure.js

# To other targets
dafny build --target:cs  # C#
dafny build --target:java  # Java
dafny build --target:go  # Go
dafny build --target:py  # Python
```

## TLA+ Correspondence

Map Dafny constructs to TLA+ for cross-model consistency:

| Dafny | TLA+ Equivalent |
|-------|-----------------|
| `class Foo { var x: int }` | `VARIABLE foo` with `foo.x ∈ Int` |
| `ghost predicate Valid() { P }` | `Invariant == P` |
| `method M() requires P ensures Q` | `M == P /\ ... /\ Q'` |
| `old(x)` | `x` (unprimed, current state) |
| `ensures x == ...` | `x' = ...` (primed, next state) |

## Additional Resources

### Reference Files
- **`references/common-errors.md`** - Comprehensive guide to Dafny verification errors, causes, and fixes (from official Dafny docs)
- **`references/dafny-quick-reference.md`** - Complete Dafny syntax reference including types, statements, expressions, specifications, and common patterns

### Example Files
- **`examples/account.dfy`** - Complete banking domain example with invariants, contracts, and transfers

### External References
- [Dafny Reference Manual](https://dafny.org/latest/DafnyRef/DafnyRef) - Complete language specification
- [Dafny Tutorial](https://dafny.org/latest/OnlineTutorial/guide) - Interactive getting started guide
- [Dafny FAQ](http://dafny.org/dafny/HowToFAQ/) - Common questions and troubleshooting
- [Dafny Error Catalog](https://dafny.org/latest/HowToFAQ/Errors) - Searchable error message reference
