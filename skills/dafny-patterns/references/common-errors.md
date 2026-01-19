# Dafny Errors Reference

> **Source**: This reference consolidates information from the [Dafny Error Catalog](https://dafny.org/latest/HowToFAQ/Errors) and [How-to FAQ Guide](http://dafny.org/dafny/HowToFAQ/).

## Syntax Errors

Syntax errors occur before verification and must be fixed first.

### Predicate Return Type Error

**Error**: "unexpected token" or "expected" near predicate return type

| Aspect | Details |
|--------|---------|
| **Cause** | Adding `: bool` return type to a predicate |
| **Fix** | Remove the return type—predicates implicitly return `bool` |

```dafny
// ❌ WRONG: predicate with explicit return type
predicate IsPositive(x: int): bool {  // Syntax error!
  x > 0
}

// ✅ CORRECT: predicate without return type
predicate IsPositive(x: int) {
  x > 0
}
```

**Why this happens**: In many languages, boolean-returning functions need explicit types. Dafny predicates are special—they ALWAYS return `bool`, so specifying it is both redundant and invalid syntax.

### Function Missing Return Type Error

**Error**: "a function must have a return type"

| Aspect | Details |
|--------|---------|
| **Cause** | Omitting the return type from a function |
| **Fix** | Add `: ReturnType` after parameters |

```dafny
// ❌ WRONG: function without return type
function Square(x: int) {  // Error: missing return type
  x * x
}

// ✅ CORRECT: function with return type
function Square(x: int): int {
  x * x
}
```

### Method vs Function Return Confusion

**Error**: Various syntax errors around return declarations

| Construct | Return Syntax | Example |
|-----------|---------------|---------|
| `method` | `returns (name: Type)` | `method Foo() returns (r: int)` |
| `function` | `: Type` | `function Foo(): int` |
| `predicate` | None | `predicate Foo()` |

```dafny
// ❌ WRONG: method with function-style return
method Compute(x: int): int { ... }  // Error!

// ✅ CORRECT: method with proper returns clause
method Compute(x: int) returns (result: int) { ... }

// ❌ WRONG: function with method-style return
function Compute(x: int) returns (result: int) { ... }  // Error!

// ✅ CORRECT: function with colon return type
function Compute(x: int): int { ... }
```

---

## Understanding Verification Errors

There are two main causes for Dafny verification errors:

1. **Specifications inconsistent with code** - The spec doesn't match what the code does
2. **Insufficient prover hints** - The prover needs help to establish the proof

Differentiating between these can be challenging. See [Verification Optimization](https://dafny.org/latest/VerificationOptimization/VerificationOptimization) for guidance on helping the prover.

## Common Verification Errors

### Precondition Errors

**"precondition might not hold"**

| Aspect | Details |
|--------|---------|
| **Cause** | A method is called without ensuring its requirements are met at the call site |
| **Fix Options** | 1) Add assertions before the call to establish preconditions, 2) Strengthen the caller's preconditions, 3) Weaken the callee's preconditions |

```dafny
// Error: precondition might not hold
method Caller(x: int) {
  Divide(10, x);  // Error: x might be 0
}

method Divide(a: int, b: int) returns (r: int)
  requires b != 0
{
  r := a / b;
}

// Fix: ensure precondition at call site
method CallerFixed(x: int)
  requires x != 0
{
  Divide(10, x);  // OK
}
```

### Postcondition Errors

**"postcondition might not hold"**

| Aspect | Details |
|--------|---------|
| **Cause** | The method body doesn't guarantee what the `ensures` clause promises |
| **Fix Options** | 1) Fix the implementation, 2) Weaken the postcondition, 3) Add loop invariants if loops are involved |

> **Common pitfall**: A typical reason postconditions fail is that there are other exit paths from the method or function. You can assert a condition right before a return, but if there are early returns or exceptions, the postcondition applies to all paths.
>
> *Source: [FAQFailingPost](https://dafny.org/latest/HowToFAQ/FAQFailingPost)*

```dafny
// Error: postcondition might not hold
method Double(x: int) returns (r: int)
  ensures r == 2 * x
{
  r := x + x + 1;  // Bug: off by one
}

// Fix: correct implementation
method DoubleFixed(x: int) returns (r: int)
  ensures r == 2 * x
{
  r := x + x;  // Correct
}
```

### Invariant Errors

**"invariant might not hold" / "loop invariant might not be maintained"**

| Aspect | Details |
|--------|---------|
| **Cause** | A loop body doesn't preserve the loop invariant, or class invariant violated |
| **Fix Options** | 1) Strengthen the invariant, 2) Fix the loop body, 3) Add intermediate assertions |

> **Object invariant quirk**: If you have an assertion about an object (of class type) and a loop that doesn't mention (read, modify) the object, Dafny may still fail to establish the assertion after the loop. This is because Dafny's frame reasoning needs explicit `modifies` clauses.
>
> *Source: [Dafny FAQ](http://dafny.org/dafny/HowToFAQ/)*

```dafny
// Error: loop invariant might not be maintained
method Sum(n: nat) returns (s: nat)
  ensures s == n * (n + 1) / 2
{
  s := 0;
  var i := 0;
  while i < n
    invariant s == i * (i + 1) / 2  // Missing: i <= n
  {
    i := i + 1;
    s := s + i;
  }
}

// Fix: complete invariant
method SumFixed(n: nat) returns (s: nat)
  ensures s == n * (n + 1) / 2
{
  s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == i * (i + 1) / 2
  {
    i := i + 1;
    s := s + i;
  }
}
```

### Termination Errors

**"decreases might not decrease" / "cannot prove termination"**

| Aspect | Details |
|--------|---------|
| **Cause** | A recursive function or loop doesn't have a provably decreasing termination measure |
| **Fix Options** | 1) Add explicit `decreases` clause, 2) Fix the recursion structure, 3) Use `decreases *` to disable check (not recommended) |

```dafny
// Error: cannot prove termination
function Fib(n: nat): nat
{
  if n < 2 then n else Fib(n-1) + Fib(n-2)
}
// Actually OK - Dafny infers decreases n

// Needs explicit decreases for mutual recursion
function IsEven(n: nat): bool
  decreases n
{
  if n == 0 then true else IsOdd(n-1)
}

function IsOdd(n: nat): bool
  decreases n
{
  if n == 0 then false else IsEven(n-1)
}
```

### Assertion Errors

**"assertion might not hold"**

| Aspect | Details |
|--------|---------|
| **Cause** | An explicit `assert` statement cannot be proven from available context |
| **Fix Options** | 1) Add intermediate assertions to guide prover, 2) Strengthen preconditions, 3) Add lemmas |

## Compilation and Resolution Errors

### Ghost Context Errors

**"ghost variable in non-ghost context"**

| Aspect | Details |
|--------|---------|
| **Cause** | A ghost expression affects compiled code execution |
| **Fix** | Restrict ghost variables to specifications only (requires, ensures, invariants, asserts) |

```dafny
// Error: ghost in non-ghost context
ghost var g: int := 5;
var x: int := g;  // Cannot use ghost in compiled code

// OK: ghost only in specifications
ghost var g: int := 5;
method M() requires g > 0 { }  // OK in requires
```

### Frame Errors

**"insufficient reads clause to invoke function"**

| Aspect | Details |
|--------|---------|
| **Cause** | Function reads heap state not covered by its `reads` clause |
| **Fix** | Add missing heap locations to `reads` clause |

*Source: [ERROR_InsufficientReads](https://dafny.org/v4.6.0/HowToFAQ/ERROR_InsufficientReads)*

```dafny
class Cell { var data: int }

// Error: reads clause insufficient
function GetData(c: Cell): int
{
  c.data  // Error: reads nothing but accesses c.data
}

// Fix: declare what the function reads
function GetDataFixed(c: Cell): int
  reads c
{
  c.data
}
```

## Debugging Strategies

### 1. Add Intermediate Assertions

Break complex proofs into steps:

```dafny
method Complex(x: int) returns (r: int)
  requires x > 0
  ensures r > x
{
  var temp := x * 2;
  assert temp > x;  // Help prover see intermediate fact
  r := temp + 1;
  assert r > temp;  // Step by step
}
```

### 2. Use Calc Statements

For complex equational reasoning:

```dafny
lemma Associative(a: int, b: int, c: int)
  ensures (a + b) + c == a + (b + c)
{
  calc {
    (a + b) + c;
    == { /* by associativity */ }
    a + (b + c);
  }
}
```

### 3. Extract Lemmas

When proofs are complex, extract helper lemmas:

```dafny
lemma SumBound(a: nat, b: nat)
  ensures a + b >= a
  ensures a + b >= b
{ }

method UsesBound(x: nat, y: nat) returns (z: nat)
  ensures z >= x
{
  SumBound(x, y);  // Invoke lemma to establish facts
  z := x + y;
}
```

### 4. Use reveal Statements

For opaque functions:

```dafny
opaque function Secret(x: int): int { x * 2 }

method UseSecret(x: int)
  ensures Secret(x) == x * 2
{
  reveal Secret();  // Make definition available
}
```

## External References

- [Dafny Error Catalog](https://dafny.org/latest/HowToFAQ/Errors) - Complete searchable list
- [Verification Optimization](https://dafny.org/latest/VerificationOptimization/VerificationOptimization) - Helping the prover
- [Dafny FAQ](http://dafny.org/dafny/HowToFAQ/) - Common questions and answers
- [Dafny Reference Manual](https://dafny.org/latest/DafnyRef/DafnyRef) - Complete language specification
