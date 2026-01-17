---
description: Display current specification state and assertion coverage
argument-hint: [filter]
allowed-tools: Read
model: haiku
---

# Show Specification

Display current state of formal specifications and assertion coverage.

## Load State

Read from:
- `specs/assertions.json` - Assertion manifest
- `specs/dafny/*.dfy` - Structure specifications
- `specs/tla/*.tla` - Behavior specifications

If specs don't exist, report: "No specifications found. Run `/probe-domain` to start."

## Filter Options

If $ARGUMENTS provided, filter display:
- `structure` - Show only Dafny/structure assertions
- `behavior` - Show only TLA+/behavior assertions
- `pending` - Show only unconfirmed assertions
- `confirmed` - Show only confirmed assertions
- `A-XXX` - Show specific assertion by ID

## Assertion Summary

Display assertion statistics:

```
Assertion Status
================
Total assertions: 47

By Status:
  ✓ Confirmed:  32 (68%)
  ○ Pending:    12 (26%)
  ✗ Denied:      3 (6%)

By Category:
  Structure (Dafny): 28
    - Data constraints:  8
    - Invariants:       10
    - Preconditions:     6
    - Postconditions:    4

  Behavior (TLA+): 19
    - Safety:           7
    - Liveness:         5
    - Ordering:         4
    - Mutual exclusion: 3
```

## Assertion List

For each assertion, show:

```
[A-001] ✓ CONFIRMED (structure/invariant)
  "Account balance never negative"
  → Dafny: invariant balance >= 0
  Source: user-interview-001

[A-002] ✓ CONFIRMED (structure/precondition)
  "Can only withdraw if sufficient funds"
  → Dafny: requires amount <= balance
  Source: user-interview-001

[A-003] ○ PENDING (behavior/liveness)
  "Every request eventually gets a response"
  → TLA+: Request ~> Response
  Source: archetype-web-service
```

## Formal Spec Overview

### Dafny Structure

Show outline of `specs/dafny/structure.dfy`:

```
specs/dafny/structure.dfy
=========================
Types:
  - Age (refinement: 0 < x < 150)
  - Price (refinement: x >= 0)
  - Status (enum: Pending | Active | Closed)

Classes:
  - Account
    Invariants:
      - balance >= 0
    Methods:
      - Withdraw(amount) requires/ensures...
      - Deposit(amount) requires/ensures...

  - Order
    Invariants:
      - |items| > 0
    Methods:
      - AddItem(...) requires/ensures...

Predicates:
  - ValidEmail(s)
  - UniqueEmails(users)
```

### TLA+ Behavior

Show outline of `specs/tla/behavior.tla`:

```
specs/tla/behavior.tla
======================
Variables:
  - orderState
  - balance
  - transactions

Actions:
  - Deposit(amount)
  - Withdraw(amount)
  - ConfirmOrder
  - ShipOrder
  - CancelOrder

Invariants (Safety):
  - BalanceNonNegative: balance >= 0
  - NoDoubleProcessing: order not processed twice

Properties (Liveness):
  - OrderCompletion: pending ~> (delivered \/ cancelled)
  - RequestResponse: request ~> response

Fairness:
  - WF_vars(ProcessRequest)
```

## Coverage Analysis

### Actor × Capability Matrix

```
Coverage Matrix
===============
                  │ Create │ Read │ Update │ Delete │ Special
──────────────────┼────────┼──────┼────────┼────────┼─────────
Customer          │   ✓    │  ✓   │   ✓    │   ○    │ checkout ✓
Admin             │   ✓    │  ✓   │   ✓    │   ✓    │ suspend ○
Background Job    │   -    │  ✓   │   ✓    │   -    │ cleanup ✓

Legend: ✓ = covered, ○ = partial, - = N/A
```

### Verification Status

```
Verification Status
===================
Dafny: Last run 2024-01-15 10:30 - PASSED
  - 15 methods verified
  - 8 invariants checked

TLC: Last run 2024-01-15 10:32 - PASSED
  - 1,247 states explored
  - 5 properties checked
  - No deadlocks found

Cross-model: CONSISTENT
```

## Dependency Graph

Show how assertions relate:

```
Assertion Dependencies
======================
A-001 (balance >= 0)
  └── Implies: A-002 (withdraw requires balance check)

A-010 (order state machine)
  ├── Uses: A-011 (confirm transition)
  ├── Uses: A-012 (ship transition)
  └── Uses: A-013 (cancel transition)
```

## Output Format

If filter specified, show only matching content.

If no filter, show summary followed by detailed list.

Conclude with:
- Total coverage percentage
- Next recommended action (interview for pending, verify after changes, generate if ready)
