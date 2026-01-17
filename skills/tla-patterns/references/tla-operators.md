# TLA+ Operators Reference

Comprehensive reference for TLA+ operators, temporal logic, and model checking.

> **Source**: [TLA+ Cheatsheet (PDF)](https://lamport.azurewebsites.net/tla/summary-standalone.pdf)

## Table of Contents

- [Logic Operators](#logic-operators)
- [Set Operators](#set-operators)
- [Function Operators](#function-operators)
- [Sequence Operators](#sequence-operators)
- [Temporal Operators](#temporal-operators)
- [Action Operators](#action-operators)
- [Standard Modules](#standard-modules)

---

## Logic Operators

### Boolean Operators

| Operator | Meaning | Example |
|----------|---------|---------|
| `/\` | AND (conjunction) | `P /\ Q` |
| `\/` | OR (disjunction) | `P \/ Q` |
| `~` | NOT (negation) | `~P` |
| `=>` | IMPLIES | `P => Q` |
| `<=>` | IFF (equivalence) | `P <=> Q` |
| `TRUE` | True constant | |
| `FALSE` | False constant | |

### Quantifiers

```tla
\* Universal quantification: for all x in S, P(x) holds
\A x \in S: P(x)

\* Existential quantification: there exists x in S such that P(x)
\E x \in S: P(x)

\* Examples
\A i \in 1..10: i > 0           \* All in range are positive
\E i \in 1..10: i * i = 25      \* Some square is 25
\A x, y \in S: x # y => P(x, y) \* For all distinct pairs
```

### Conditional

```tla
\* IF-THEN-ELSE
IF condition THEN expr1 ELSE expr2

\* CASE expression
CASE x = 1 -> "one"
  [] x = 2 -> "two"
  [] OTHER -> "other"
```

### LET-IN

```tla
LET
  x == expr1
  y == expr2
IN
  x + y
```

---

## Set Operators

### Basic Set Operations

| Operator | Meaning | Example |
|----------|---------|---------|
| `\in` | Element of | `x \in S` |
| `\notin` | Not element of | `x \notin S` |
| `\cup` or `\union` | Union | `S \cup T` |
| `\cap` or `\intersect` | Intersection | `S \cap T` |
| `\` or `\setminus` | Difference | `S \ T` |
| `\subseteq` | Subset or equal | `S \subseteq T` |
| `\subset` | Proper subset | `S \subset T` |
| `=` | Set equality | `S = T` |
| `#` | Not equal | `S # T` |

### Set Constructors

```tla
\* Enumeration
{1, 2, 3}
{"a", "b", "c"}

\* Range (integers)
1..10              \* {1, 2, 3, ..., 10}

\* Set comprehension (filter)
{x \in S: P(x)}    \* Elements of S satisfying P

\* Set mapping
{f(x): x \in S}    \* Apply f to each element

\* Power set
SUBSET S           \* Set of all subsets of S

\* Cartesian product
S \X T             \* Set of all pairs (s, t)
```

### Set Functions

```tla
EXTENDS FiniteSets

Cardinality(S)     \* Number of elements (finite sets only)
IsFiniteSet(S)     \* TRUE if S is finite
```

---

## Function Operators

### Function Definition

```tla
\* Function literal (record-like)
[x \in S |-> expr]

\* Examples
[n \in 1..10 |-> n * n]        \* Squares function
[s \in {"a", "b"} |-> 0]       \* Initialize to 0

\* Record (function with string domain)
[field1 |-> val1, field2 |-> val2]
```

### Function Application

```tla
f[x]               \* Apply function f to x
f["field"]         \* Access record field
r.field            \* Shorthand for r["field"]
```

### Function Update (EXCEPT)

```tla
\* Update single value
[f EXCEPT ![x] = newval]

\* Update multiple values
[f EXCEPT ![x] = v1, ![y] = v2]

\* Use @ to refer to old value
[f EXCEPT ![x] = @ + 1]

\* Nested update
[f EXCEPT ![x][y] = newval]
[r EXCEPT !.field = newval]
```

### Function Set

```tla
\* Set of all functions from S to T
[S -> T]

\* Example: all possible states
[Processes -> {"idle", "running", "done"}]
```

---

## Sequence Operators

```tla
EXTENDS Sequences

\* Sequence literal
<<1, 2, 3>>
<<>>               \* Empty sequence

\* Basic operations
Len(s)             \* Length
Head(s)            \* First element
Tail(s)            \* All but first
Last(s)            \* Last element (from TLC)

\* Indexing (1-based)
s[1]               \* First element
s[Len(s)]          \* Last element

\* Concatenation
s \o t             \* Concatenate sequences
Append(s, x)       \* Add to end

\* Subsequence
SubSeq(s, m, n)    \* Elements m through n

\* Conversion
SeqToSet(s)        \* Convert to set (from TLC)
```

---

## Temporal Operators

### Basic Temporal

| Operator | Name | Meaning |
|----------|------|---------|
| `[]P` | Always | P is true in all states |
| `<>P` | Eventually | P is true in some future state |
| `[]<>P` | Infinitely often | P is true infinitely often |
| `<>[]P` | Eventually always | P becomes and stays true |

### Leads-To

```tla
\* P leads to Q: whenever P is true, Q eventually becomes true
P ~> Q

\* Equivalent to
[](P => <>Q)
```

### Examples

```tla
\* Safety: balance never negative
[]( balance >= 0 )

\* Liveness: every request eventually gets response
[](request => <>response)
\* Or using leads-to
request ~> response

\* Fairness: system eventually stabilizes
<>[]stable

\* Repeated possibility: can always return to initial
[]<>(state = "init")
```

---

## Action Operators

### Prime Notation

```tla
\* Primed variable: value in next state
x'                 \* x in next state
x                  \* x in current state

\* Action: relates current and next state
x' = x + 1         \* x increases by 1
```

### UNCHANGED

```tla
\* Variable doesn't change
UNCHANGED x
UNCHANGED <<x, y, z>>

\* Equivalent to
x' = x
<<x', y', z'>> = <<x, y, z>>
```

### Action Operators

```tla
\* Stuttering: either A or variables unchanged
[A]_vars

\* Non-stuttering: A must happen
<A>_vars

\* Examples
[][Next]_vars      \* Next or stutter
<><<Next>>_vars    \* Eventually a real step
```

### Enabled

```tla
\* TRUE if action A is possible
ENABLED A

\* Example: check if withdraw is possible
ENABLED Withdraw
```

### Fairness

```tla
\* Weak fairness: if continuously enabled, eventually happens
WF_vars(A)

\* Strong fairness: if repeatedly enabled, eventually happens
SF_vars(A)

\* Typical spec pattern
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
```

---

## Standard Modules

### Integers

```tla
EXTENDS Integers

\* Constants
Int                \* Set of all integers
Nat                \* Set of natural numbers (0, 1, 2, ...)

\* Operators
+, -, *, \div, %   \* Arithmetic
<, >, <=, >=       \* Comparison
a..b               \* Range {a, a+1, ..., b}
```

### Naturals

```tla
EXTENDS Naturals

Nat                \* {0, 1, 2, ...}
\* Same arithmetic but domain is Nat
```

### Reals

```tla
EXTENDS Reals

Real               \* Set of real numbers
Infinity           \* Positive infinity
/                  \* Real division
```

### Sequences

```tla
EXTENDS Sequences

Seq(S)             \* Set of all sequences over S
Len(s)             \* Length
Head(s), Tail(s)   \* First element, rest
Append(s, e)       \* Add to end
s \o t             \* Concatenation
SubSeq(s, m, n)    \* Subsequence
```

### FiniteSets

```tla
EXTENDS FiniteSets

IsFiniteSet(S)     \* TRUE if S is finite
Cardinality(S)     \* Number of elements
```

### TLC (Model Checker Extras)

```tla
EXTENDS TLC

Print(val, expr)   \* Print val, return expr
PrintT(val)        \* Print val, return TRUE
Assert(P, msg)     \* Assert P or print msg
ToString(val)      \* Convert to string
```

---

## TLC Configuration

### Basic Config File

```
\* myspec.cfg

SPECIFICATION Spec

\* Safety properties (invariants)
INVARIANT TypeOK
INVARIANT SafetyProperty

\* Liveness properties
PROPERTY LivenessProperty

\* Constants
CONSTANT
  N = 3
  Procs = {p1, p2, p3}

\* State constraints (limit state space)
CONSTRAINT
  balance <= 1000
  Len(log) <= 10
```

### Symmetry Sets

```
\* Reduce state space with symmetry
CONSTANT
  Procs = {p1, p2, p3}
SYMMETRY SymmetryPerms

\* In spec:
SymmetryPerms == Permutations(Procs)
```

---

## Common Patterns

### Type Invariant

```tla
TypeOK ==
  /\ state \in {"idle", "running", "done"}
  /\ counter \in Nat
  /\ buffer \in Seq(Message)
  /\ Len(buffer) <= MaxLen
```

### State Machine

```tla
VARIABLES state

Init == state = "idle"

Start == state = "idle" /\ state' = "running"
Finish == state = "running" /\ state' = "done"
Reset == state = "done" /\ state' = "idle"

Next == Start \/ Finish \/ Reset

Spec == Init /\ [][Next]_state /\ WF_state(Next)
```

### Mutual Exclusion

```tla
MutualExclusion == Cardinality(inCritical) <= 1

Enter(p) ==
  /\ inCritical = {}
  /\ inCritical' = {p}

Exit(p) ==
  /\ p \in inCritical
  /\ inCritical' = {}
```

### Message Passing

```tla
Send(m) ==
  /\ messages' = messages \cup {m}
  /\ UNCHANGED otherVars

Receive(m) ==
  /\ m \in messages
  /\ messages' = messages \ {m}
  /\ ProcessMessage(m)
```

---

## External References

- [TLA+ Home Page](https://lamport.azurewebsites.net/tla/tla.html)
- [TLA+ Cheatsheet (PDF)](https://lamport.azurewebsites.net/tla/summary-standalone.pdf)
- [TLA+ Repository](https://github.com/tlaplus/tlaplus)
- [TLA+ Examples](https://github.com/tlaplus/Examples)
- [Learn TLA+](https://learntla.com/)
- [TLA+ Video Course](https://lamport.azurewebsites.net/video/videos.html)
