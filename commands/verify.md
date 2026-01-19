---
description: Run formal verification on Dafny and TLA+ specs
allowed-tools: Read, Bash, AskUserQuestion
model: sonnet
---

# Verification Orchestration

Run formal verification tools and interpret results.

## Prerequisites

Check that specs exist:
- `specs/dafny/*.dfy` for structure verification
- `specs/tla/*.tla` and `specs/tla/*.cfg` for behavior verification

If no specs exist, instruct user to run `/probe-domain` and `/interview` first.

## Environment Check

Tools are run via Nix for reproducible environments. No local installation required.

If user prefers a persistent shell, provide flake.nix template location:
`${CLAUDE_PLUGIN_ROOT}/templates/flake.nix`

They can copy it to their project and run `nix develop` for a full development shell with aliases.

## Dafny Verification

See [Verification](https://dafny.org/latest/DafnyRef/DafnyRef#sec-verification) in the Dafny Reference Manual for detailed guidance on debugging verification failures.

### Run Verifier

```bash
nix-shell -p dafny --run "dafny verify specs/dafny/*.dfy" 2>&1
```

### Interpret Results

**On Success (Verified)**:
- Report: "✓ Dafny verification passed - structural specifications are consistent"
- List number of methods/invariants verified

**On Failure**:
- Parse error output to identify failing construct
- Map error back to source assertion(s) using traceability comments
- Explain failure in plain language

Common Dafny errors and explanations:

| Error Pattern | Plain Language |
|---------------|----------------|
| "precondition might not hold" | A method is called without ensuring its requirements are met |
| "postcondition might not hold" | The method body doesn't guarantee what it promises |
| "invariant might not hold" | A state constraint could be violated |
| "assertion might not hold" | An explicit assertion could be false |
| "decreases might not decrease" | A loop or recursion might not terminate |

### Suggest Fixes

For each failure:
1. Identify the specific assertion or code involved
2. Explain what condition could cause the failure
3. Propose fix options:
   - Strengthen precondition (add requires)
   - Weaken postcondition (relax ensures)
   - Add missing invariant
   - Fix implementation logic

Ask user which approach to take.

## TLA+ Model Checking

See the [TLA+ Repository](https://github.com/tlaplus/tlaplus) for tool documentation and the [TLA+ Examples](https://github.com/tlaplus/Examples) for reference specifications.

### Run TLC

```bash
nix-shell -p tlaplus --run "tlc specs/tla/behavior.tla -config specs/tla/behavior.cfg" 2>&1
```

### Interpret Results

**On Success (No errors)**:
- Report: "✓ TLC model checking passed - behavioral properties hold"
- Report state space explored (states, distinct states)

**On Invariant Violation**:
- Parse counterexample trace
- Explain the sequence of states that violates the invariant
- Map back to source assertions

**On Liveness Violation**:
- Parse the lasso-shaped counterexample
- Explain the cycle that prevents progress
- Identify missing fairness conditions or spec issues

**On Deadlock**:
- Explain that no actions are enabled from some reachable state
- Show the deadlocked state
- Suggest adding actions or fixing guards

### Common TLC Issues

| Issue | Plain Language |
|-------|----------------|
| Invariant violated | A safety property fails in some reachable state |
| Temporal property violated | A liveness property fails (something doesn't eventually happen) |
| Deadlock reached | System gets stuck with no possible next action |
| State space too large | Model is too big to check exhaustively |

For detailed TLC documentation, see the [TLA+ Cheatsheet](https://lamport.azurewebsites.net/tla/summary-standalone.pdf) or the [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html) for the video course.

### Suggest Fixes

For invariant violations:
1. Show the counterexample trace in plain language
2. Identify which state transition caused the violation
3. Propose fix: strengthen action guards, add missing checks

For liveness violations:
1. Show the cycle preventing progress
2. Identify fairness issues
3. Propose fix: add weak/strong fairness, fix action enablement

## Cross-Model Consistency

After individual verification succeeds, check cross-model consistency:

1. Every TLA+ action should preserve Dafny invariants
   - Simulate: Can TLA+ action produce state violating Dafny invariant?

2. Every Dafny method should have TLA+ counterpart
   - Check: Does each Dafny method have corresponding TLA+ action?

3. Type constraints align
   - Check: Do Dafny refinement types match TLA+ type invariants?

Report any inconsistencies found.

## Verification Summary

Provide summary:

```
Verification Results
====================
Dafny (Structure): [PASSED/FAILED]
  - Methods verified: N
  - Invariants verified: N
  - Issues: [list if any]

TLC (Behavior): [PASSED/FAILED]
  - States explored: N
  - Properties checked: N
  - Issues: [list if any]

Cross-Model: [CONSISTENT/INCONSISTENT]
  - Issues: [list if any]

Next Steps:
- [If passed] Ready for /generate to create implementation
- [If failed] Fix issues above, then re-run /verify
```

## Interactive Resolution

If verification fails, offer to help resolve:

**Question**: "Verification found issues. How would you like to proceed?"
**Options**:
- Fix automatically - Apply suggested fixes
- Explain more - Get detailed explanation of failures
- Modify assertion - Change the underlying assertion
- Skip for now - Mark issue for later
