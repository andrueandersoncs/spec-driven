---
description: Resolve contradictions found during verification
argument-hint: [assertion-id]
allowed-tools: Read, Write, Edit, AskUserQuestion
model: sonnet
---

# Conflict Resolution

Resolve contradictions found during formal verification.

## Context Loading

Read current state from:
- `specs/assertions.json` - Assertion manifest
- Last verification output (if available)

If $ARGUMENTS provides assertion ID, focus on that specific conflict.
Otherwise, process all unresolved conflicts.

## Conflict Types

### Type 1: Assertion Contradiction

Two assertions cannot both be true.

**Example**:
- A-001: "Balance can be negative (overdraft allowed)"
- A-002: "Balance must never be negative"

**Resolution Options**:
1. Keep A-001, deny A-002
2. Keep A-002, deny A-001
3. Refine both (e.g., "Balance >= -overdraftLimit")
4. Add condition (e.g., "Depends on account type")

### Type 2: Precondition Too Weak

Operation can be called in invalid state.

**Example**:
- Dafny error: "precondition might not hold"
- Method `Withdraw` requires `amount > 0` but called with unchecked input

**Resolution Options**:
1. Strengthen caller (add validation before call)
2. Weaken callee (remove or relax precondition)
3. Add intermediate check

### Type 3: Postcondition Too Strong

Implementation cannot guarantee promise.

**Example**:
- Dafny error: "postcondition might not hold"
- Method promises `balance == old(balance) - amount` but has edge cases

**Resolution Options**:
1. Fix implementation to satisfy postcondition
2. Weaken postcondition (add failure case)
3. Strengthen precondition (narrow valid inputs)

### Type 4: Invariant Violation

State constraint broken by some operation.

**Example**:
- Dafny error: "invariant might not hold"
- Operation `ApplyFee` can make `balance < 0`

**Resolution Options**:
1. Fix operation to preserve invariant
2. Weaken invariant (allow more states)
3. Add precondition to operation

### Type 5: Safety Property Violation

Bad thing can happen (TLA+).

**Example**:
- TLC counterexample: Order processed twice

**Resolution Options**:
1. Add guard to prevent duplicate processing
2. Make operation idempotent
3. Refine safety property

### Type 6: Liveness Violation

Good thing might never happen (TLA+).

**Example**:
- TLC counterexample: Request never gets response (cycle found)

**Resolution Options**:
1. Add fairness condition
2. Remove blocking condition
3. Weaken liveness property

## Resolution Process

### Step 1: Present Conflict

Explain in plain language:
- What the conflict is
- Why it's a problem
- What assertions/specs are involved

**Example Output**:
```
Conflict Found: Assertion Contradiction
=======================================

These two assertions cannot both be true:

A-015: "Users can overdraw accounts up to $100"
  → Implies balance can go to -100

A-003: "Account balance never negative"
  → Requires balance >= 0

This creates an impossible specification.
```

### Step 2: Show Evidence

For verification failures, show:
- Counterexample trace (TLA+)
- Failing proof obligation (Dafny)
- Specific line/construct involved

**Example**:
```
Counterexample Trace (TLC):
1. Initial: balance = 50
2. Withdraw(100): FAILS precondition in current spec
   OR
2. Withdraw(100): balance' = -50 (violates invariant)
```

### Step 3: Present Options

Use AskUserQuestion to present resolution options:

**Question**: "How should this conflict be resolved?"
**Options**:
- Option 1: [specific fix with description]
- Option 2: [alternative fix with description]
- Option 3: [user provides custom resolution]
- Option 4: [defer to later]

Include tradeoffs for each option:
- What it preserves
- What it gives up
- Implications for other assertions

### Step 4: Apply Resolution

Based on user choice:

**If modifying assertion**:
1. Update `specs/assertions.json`
2. Mark old assertion as "refined" with reference to new
3. Regenerate affected formal specs

**If modifying spec directly**:
1. Edit `specs/dafny/*.dfy` or `specs/tla/*.tla`
2. Update corresponding assertion
3. Re-run verification

**If deferring**:
1. Mark conflict as "deferred" in assertions.json
2. Add note about why deferred
3. Continue to other conflicts

### Step 5: Verify Resolution

After applying fix:
1. Re-run verification for affected specs
2. Check for new conflicts introduced
3. Confirm resolution successful

## Conflict Summary

After processing, report:

```
Conflict Resolution Summary
===========================
Conflicts found: 3
Resolved: 2
Deferred: 1

Resolved:
  [A-015/A-003] Overdraft vs. non-negative balance
    Resolution: Refined A-003 to "balance >= -overdraftLimit"

  [Withdraw precondition] Amount validation
    Resolution: Added caller-side validation

Deferred:
  [OrderLifecycle] Timeout behavior
    Reason: Needs product decision on timeout duration

Next Steps:
- Re-run /verify to confirm resolutions
- Address deferred conflicts when ready
```

## Batch Processing

If multiple conflicts exist, process systematically:
1. Group related conflicts
2. Resolve foundational conflicts first (they may resolve dependent ones)
3. Re-verify after each resolution
4. Present remaining conflicts

## Integration

After resolution:
- Specs are consistent
- Can proceed to `/generate` for code generation
- Deferred conflicts noted for future resolution
