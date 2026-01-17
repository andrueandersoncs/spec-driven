# Dafny Quick Reference

Comprehensive reference for Dafny syntax, types, and verification constructs.

> **Source**: [Dafny Reference Manual](https://dafny.org/latest/DafnyRef/DafnyRef)

## Table of Contents

- [Types](#types)
- [Statements](#statements)
- [Expressions](#expressions)
- [Specifications](#specifications)
- [Classes and Modules](#classes-and-modules)
- [Verification Hints](#verification-hints)

---

## Types

### Built-in Types

| Type | Description | Examples |
|------|-------------|----------|
| `int` | Unbounded integer | `0`, `-42`, `1000000` |
| `nat` | Non-negative integer | `0`, `42` |
| `real` | Real number | `3.14`, `-2.5` |
| `bool` | Boolean | `true`, `false` |
| `char` | Character | `'a'`, `'\n'` |
| `string` | Sequence of chars | `"hello"` |

### Collection Types

```dafny
// Sequence (ordered, duplicates allowed)
var xs: seq<int> := [1, 2, 3];
var first := xs[0];           // Index access
var len := |xs|;              // Length
var slice := xs[1..3];        // Slice [1,3)
var concat := xs + [4, 5];    // Concatenation

// Set (unordered, no duplicates)
var s: set<int> := {1, 2, 3};
var contains := 2 in s;       // Membership
var union := s + {4, 5};      // Union
var intersect := s * {2, 3};  // Intersection
var diff := s - {1};          // Difference
var card := |s|;              // Cardinality

// Multiset (unordered, duplicates counted)
var ms: multiset<int> := multiset{1, 1, 2};
var count := ms[1];           // Count of element (returns 2)

// Map (key-value pairs)
var m: map<string, int> := map["a" := 1, "b" := 2];
var val := m["a"];            // Lookup
var keys := m.Keys;           // Set of keys
var vals := m.Values;         // Set of values
```

### Subset Types (Refinement Types)

```dafny
// Constrained integer types
type Age = x: int | 0 < x < 150
type Positive = x: int | x > 0
type NonNegative = x: int | x >= 0

// Constrained string types
type NonEmptyString = s: string | |s| > 0
type BoundedString = s: string | |s| <= 100

// With witness (proof of non-emptiness)
type EvenInt = x: int | x % 2 == 0 witness 0
```

### Algebraic Data Types

```dafny
// Simple enumeration
datatype Status = Pending | Active | Completed | Cancelled

// With parameters
datatype Option<T> = None | Some(value: T)

datatype Result<T, E> = Ok(value: T) | Err(error: E)

// Usage
var opt: Option<int> := Some(42);
match opt {
  case None => print "empty"
  case Some(v) => print v
}

// Discriminator predicates
if opt.Some? { ... }
```

---

## Statements

### Variable Declaration

```dafny
var x: int := 0;              // Typed
var y := 42;                  // Inferred
var a, b := 1, 2;             // Multiple
ghost var g := 0;             // Ghost (spec only)
```

### Control Flow

```dafny
// If-else
if condition {
  ...
} else if other {
  ...
} else {
  ...
}

// While loop (requires invariants)
while i < n
  invariant 0 <= i <= n
  invariant sum == SumTo(i)
{
  sum := sum + i;
  i := i + 1;
}

// For loop
for i := 0 to n
  invariant ...
{
  ...
}

// Match expression
match status {
  case Pending => ...
  case Active => ...
  case Completed | Cancelled => ...
}
```

### Assertions

```dafny
assert condition;             // Must be provable
assume condition;             // Assume true (unsound!)
expect condition;             // Runtime check
```

---

## Expressions

### Quantifiers

```dafny
// Universal: all elements satisfy predicate
forall x :: P(x)
forall x: int :: x > 0 ==> x * x > 0
forall i :: 0 <= i < |xs| ==> xs[i] > 0

// Existential: some element satisfies predicate
exists x :: P(x)
exists i :: 0 <= i < |xs| && xs[i] == target
```

### Set Comprehensions

```dafny
// Set builder notation
var evens := set x | 0 <= x < 100 && x % 2 == 0;
var squares := set x | x in evens :: x * x;
```

### Sequence Comprehensions

```dafny
// Generate sequence
var zeros := seq(10, _ => 0);           // [0, 0, ..., 0]
var indices := seq(10, i => i);         // [0, 1, ..., 9]
var doubled := seq(|xs|, i => xs[i] * 2);
```

### Let Expressions

```dafny
var result := (
  var temp := expensive();
  temp + 1
);
```

### Old Expression

```dafny
// In postcondition: refer to pre-state
ensures balance == old(balance) + amount
```

---

## Specifications

### Method Contracts

```dafny
method MethodName(param: Type) returns (result: Type)
  requires precondition          // Caller's obligation
  ensures postcondition          // Method's guarantee
  modifies this, other           // What can change
  decreases variant              // Termination proof
{
  // Implementation
}
```

### Function Contracts

```dafny
function FunctionName(param: Type): ReturnType
  requires precondition
  ensures postcondition
  reads this                     // What can be read
  decreases variant
{
  expression
}

// Ghost function (spec only)
ghost function GhostFn(x: int): int { x + 1 }
```

### Predicates

```dafny
// Boolean-returning function
predicate Valid()
  reads this
{
  balance >= 0 && limit >= 0
}

// Ghost predicate (verification only)
ghost predicate Sorted(xs: seq<int>) {
  forall i, j :: 0 <= i < j < |xs| ==> xs[i] <= xs[j]
}
```

### Loop Invariants

```dafny
while i < n
  invariant 0 <= i <= n                    // Bounds
  invariant sum == SumSpec(xs[..i])        // Partial result
  invariant forall j :: 0 <= j < i ==> P(j) // Processed elements
{
  ...
}
```

---

## Classes and Modules

### Class Definition

```dafny
class Account {
  var balance: int
  var limit: int

  // Object invariant as predicate
  ghost predicate Valid()
    reads this
  {
    balance >= -limit && limit >= 0
  }

  constructor(initial: int)
    requires initial >= 0
    ensures Valid()
    ensures balance == initial
    ensures limit == 0
  {
    balance := initial;
    limit := 0;
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

### Modules

```dafny
module Finance {
  datatype Currency = USD | EUR | GBP

  class Account { ... }

  function Convert(amount: real, from: Currency, to: Currency): real
  { ... }
}

// Import
import Finance
import F = Finance              // Alias
import opened Finance           // Unqualified access
```

---

## Verification Hints

### Assert and Calc

```dafny
// Assert to help verifier
assert x > 0;
assert xs[i] in set x | x in xs;

// Calculation proof
calc {
  x + y;
  == { /* hint */ }
  y + x;
  <= { /* hint */ }
  2 * max(x, y);
}
```

### Lemmas

```dafny
lemma SumLemma(xs: seq<int>, ys: seq<int>)
  ensures Sum(xs + ys) == Sum(xs) + Sum(ys)
{
  // Proof by induction
  if xs == [] {
    // Base case
  } else {
    // Inductive case
    SumLemma(xs[1..], ys);
  }
}

// Call lemma to help verification
SumLemma(a, b);
assert Sum(a + b) == Sum(a) + Sum(b);
```

### Revealing Functions

```dafny
// Opaque function (hidden definition)
function {:opaque} ExpensiveComputation(x: int): int { ... }

// Reveal when needed
reveal ExpensiveComputation();
```

---

## Common Patterns

### Class Invariant Pattern

```dafny
class MyClass {
  var data: seq<int>
  var cached: int

  ghost predicate Valid()
    reads this
  {
    cached == Sum(data)
  }

  constructor()
    ensures Valid()
  {
    data := [];
    cached := 0;
  }

  method Add(x: int)
    requires Valid()
    modifies this
    ensures Valid()
  {
    data := data + [x];
    cached := cached + x;
  }
}
```

### Frame Conditions

```dafny
method UpdateEmail(newEmail: string)
  requires Valid()
  requires ValidEmail(newEmail)
  modifies this
  ensures Valid()
  ensures email == newEmail
  // Frame: what doesn't change
  ensures name == old(name)
  ensures balance == old(balance)
{
  email := newEmail;
}
```

### Conditional Postcondition

```dafny
method Find(xs: seq<int>, target: int) returns (index: int)
  ensures index >= 0 ==> index < |xs| && xs[index] == target
  ensures index < 0 ==> forall i :: 0 <= i < |xs| ==> xs[i] != target
{
  ...
}
```

---

## External References

- [Dafny Reference Manual](https://dafny.org/latest/DafnyRef/DafnyRef)
- [Dafny Tutorial](https://dafny.org/latest/OnlineTutorial/guide)
- [Dafny FAQ](http://dafny.org/dafny/HowToFAQ/)
- [Dafny Error Catalog](https://dafny.org/latest/HowToFAQ/Errors)
- [Dafny GitHub](https://github.com/dafny-lang/dafny)
