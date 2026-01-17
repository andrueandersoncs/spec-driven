---
name: TLA+ Patterns
description: This skill should be used when writing TLA+ specifications, defining state machines, specifying temporal properties (liveness, safety), model checking with TLC, or when the user asks "write a TLA+ spec", "model this behavior", "check this property", "verify concurrency", "define a state machine", or "check for deadlocks".
version: 0.1.0
---

# TLA+ Patterns

Write behavioral specifications using TLA+ temporal logic.

## Core Concepts

TLA+ models **behavior**: what is true across sequences of states over time.

| Construct | Purpose | Verification |
|-----------|---------|--------------|
| VARIABLES | System state | Defines state space |
| Init | Initial states | Starting conditions |
| Actions | State transitions | How system evolves |
| Invariants | Safety properties | Always true |
| Temporal | Liveness properties | Eventually true |
| Fairness | Progress guarantees | Actions eventually occur |

## File Organization

Organize TLA+ specs in `specs/tla/`:

```
specs/tla/
├── behavior.tla       # Main behavioral spec
├── behavior.cfg       # TLC configuration
└── domains/           # Domain-specific modules
    ├── auth.tla
    └── workflow.tla
```

## Basic Structure

### Minimal Spec Template

```tla
---------------------------- MODULE behavior ----------------------------
EXTENDS Integers, Sequences, FiniteSets

\* State variables
VARIABLES state, data

\* Type invariant
TypeOK ==
    /\ state \in {"idle", "working", "done"}
    /\ data \in Int

\* Initial state
Init ==
    /\ state = "idle"
    /\ data = 0

\* Actions
DoWork ==
    /\ state = "idle"
    /\ state' = "working"
    /\ data' = data + 1

Complete ==
    /\ state = "working"
    /\ state' = "done"
    /\ UNCHANGED data

\* Next state relation
Next == DoWork \/ Complete

\* Fairness
Fairness == WF_<<state, data>>(Next)

\* Specification
Spec == Init /\ [][Next]_<<state, data>> /\ Fairness

==========================================================================
```

### TLC Configuration File

```
\* behavior.cfg
SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT SafetyProperty
PROPERTY LivenessProperty
```

## State Machines

### Pattern: Simple State Machine

```tla
\* Natural language: "Order goes through pending, confirmed, shipped, delivered"
VARIABLES orderState

States == {"pending", "confirmed", "shipped", "delivered", "cancelled"}

Init == orderState = "pending"

Confirm == orderState = "pending" /\ orderState' = "confirmed"
Ship == orderState = "confirmed" /\ orderState' = "shipped"
Deliver == orderState = "shipped" /\ orderState' = "delivered"
Cancel == orderState \in {"pending", "confirmed"} /\ orderState' = "cancelled"

Next == Confirm \/ Ship \/ Deliver \/ Cancel
```

### Pattern: State Machine with Data

```tla
\* Natural language: "Account tracks balance through transactions"
VARIABLES balance, transactions

TypeOK ==
    /\ balance \in Int
    /\ transactions \in Seq([type: {"deposit", "withdraw"}, amount: Nat])

Init ==
    /\ balance = 0
    /\ transactions = <<>>

Deposit(amount) ==
    /\ amount > 0
    /\ balance' = balance + amount
    /\ transactions' = Append(transactions, [type |-> "deposit", amount |-> amount])

Withdraw(amount) ==
    /\ amount > 0
    /\ amount <= balance
    /\ balance' = balance - amount
    /\ transactions' = Append(transactions, [type |-> "withdraw", amount |-> amount])

Next == \E a \in 1..100: Deposit(a) \/ Withdraw(a)
```

## Safety Properties

Safety: something bad never happens.

### Pattern: Invariant Safety

```tla
\* Natural language: "Balance never negative"
BalanceNonNegative == balance >= 0

\* Natural language: "At most one writer at a time"
MutualExclusion == Cardinality(writers) <= 1

\* Natural language: "Never process same order twice"
NoDoubleProcessing ==
    \A o \in orders: Cardinality({p \in processed: p.orderId = o.id}) <= 1
```

### Pattern: Action Safety

```tla
\* Natural language: "Delete only after backup"
SafeDelete ==
    [][Delete => backedUp]_vars

\* Natural language: "Send only if authenticated"
AuthenticatedSend ==
    [][Send => authenticated]_vars
```

## Liveness Properties

Liveness: something good eventually happens.

### Pattern: Leads-To

```tla
\* Natural language: "Every request eventually gets a response"
RequestResponse == Request ~> Response

\* Natural language: "Pending orders eventually complete or cancel"
OrderCompletion ==
    orderState = "pending" ~> (orderState = "delivered" \/ orderState = "cancelled")
```

### Pattern: Eventually Always

```tla
\* Natural language: "System eventually stabilizes"
EventualStability == <>[]stable

\* Natural language: "Can always return to idle"
ReturnToIdle == []<>(state = "idle")
```

## Fairness

Fairness prevents unrealistic infinite stuttering.

### Pattern: Weak Fairness

```tla
\* Natural language: "If action is continuously enabled, it eventually happens"
\* Use for actions that might be disabled temporarily
Fairness == WF_vars(ProcessRequest)

\* Multiple actions
AllFair ==
    /\ WF_vars(Deposit)
    /\ WF_vars(Withdraw)
    /\ WF_vars(Process)
```

### Pattern: Strong Fairness

```tla
\* Natural language: "If action is repeatedly enabled, it eventually happens"
\* Use for actions that may be repeatedly disabled/enabled
Fairness == SF_vars(RetryOperation)
```

## Concurrency Patterns

### Pattern: Mutual Exclusion

```tla
\* Natural language: "Only one process in critical section"
VARIABLES inCritical

TypeOK == inCritical \subseteq Processes

MutualExclusion == Cardinality(inCritical) <= 1

Enter(p) ==
    /\ inCritical = {}
    /\ inCritical' = {p}

Exit(p) ==
    /\ p \in inCritical
    /\ inCritical' = {}
```

### Pattern: Reader-Writer Lock

```tla
\* Natural language: "Multiple readers or one writer, not both"
VARIABLES readers, writer

TypeOK ==
    /\ readers \in SUBSET Processes
    /\ writer \in Processes \union {None}

RWInvariant ==
    /\ writer # None => readers = {}
    /\ readers # {} => writer = None

StartRead(p) ==
    /\ writer = None
    /\ readers' = readers \union {p}
    /\ UNCHANGED writer

StartWrite(p) ==
    /\ writer = None
    /\ readers = {}
    /\ writer' = p
    /\ UNCHANGED readers
```

### Pattern: Producer-Consumer

```tla
\* Natural language: "Producers add to bounded queue, consumers remove"
VARIABLES queue
CONSTANT MaxSize

BoundedQueue == Len(queue) <= MaxSize

Produce(item) ==
    /\ Len(queue) < MaxSize
    /\ queue' = Append(queue, item)

Consume ==
    /\ Len(queue) > 0
    /\ queue' = Tail(queue)
```

## Model Checking Configuration

### Basic Config

```
\* behavior.cfg
SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT SafetyInvariant
PROPERTY LivenessProperty
```

### Constants

```
\* Define constants for model checking
CONSTANT
    Processes = {p1, p2, p3}
    MaxBalance = 1000
    MaxItems = 10
```

### State Constraints (for finite model checking)

```
\* Limit state space for tractable checking
CONSTRAINT
    balance <= 10000
    Len(transactions) <= 20
```

## Running TLC

```bash
# Basic check
tlc behavior.tla -config behavior.cfg

# With workers
tlc -workers 4 behavior.tla -config behavior.cfg

# Generate traces
tlc -dump dot states.dot behavior.tla

# Check specific depth
tlc -depth 100 behavior.tla
```

### Interpreting Results

| Result | Meaning | Action |
|--------|---------|--------|
| `No errors` | All properties hold | Spec is consistent |
| `Invariant X violated` | Safety property fails | Fix spec or weaken property |
| `Temporal property violated` | Liveness fails | Add fairness or fix spec |
| `Deadlock reached` | No enabled actions | Add action or fix guards |
| `State space too large` | Model too big | Add constraints or symmetry |

## Dafny Correspondence

Map TLA+ constructs to Dafny for cross-model consistency:

| TLA+ | Dafny Equivalent |
|------|------------------|
| `VARIABLE x` | `var x` in class |
| `TypeOK` | `invariant` |
| `Action == P /\ x' = E` | `method requires P ensures x == E` |
| `[][Action]_vars` | (implicit in method contracts) |
| Unprimed `x` | `old(x)` in postcondition |
| Primed `x'` | `x` in postcondition |

## Additional Resources

### Example Files
- **`examples/account.tla`** - Complete banking state machine with safety and liveness properties

### External References
- [TLA+ Language Manual](https://lamport.azurewebsites.net/tla/tla.html)
- [Learn TLA+](https://learntla.com/)
