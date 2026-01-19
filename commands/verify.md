---
description: Run formal verification on Dafny and TLA+ specs
allowed-tools: Read, Bash, AskUserQuestion
model: sonnet
---

# Verification Orchestration

Run formal verification tools and interpret results with progressive disclosure.

## Prerequisites

Check that specs exist:
- `specs/dafny/*.dfy` for structure verification
- `specs/tla/*.tla` and `specs/tla/*.cfg` for behavior verification

If no specs exist, instruct user to run `/probe-domain` and `/interview` first.

## Quick Verification (Recommended Default)

Run all verification with summary output:

```bash
bash ${CLAUDE_PLUGIN_ROOT}/scripts/verify-all.sh --summary
```

This provides a one-line status for each tool. If verification passes, proceed to inform user and suggest `/generate`.

## Handling Verification Failures

If summary shows failures, use progressive disclosure to avoid overwhelming the user.

### Step 1: Show Summary First

Parse the summary to identify which tool failed:
- Dafny failures → structural specification issues
- TLC failures → behavioral specification issues

### Step 2: Ask User for Detail Level

**Question**: "Verification found issues. How much detail would you like?"
**Options**:
- Show error list with locations (recommended for fixing)
- Show full output for first error only
- Show all details (may be verbose)
- Skip details, let me try to fix automatically

### Step 3: Get Detailed Output Based on Choice

**For Dafny errors** (if user wants details):
```bash
bash ${CLAUDE_PLUGIN_ROOT}/scripts/run-dafny-verify.sh --errors
```

**For TLC errors** (if user wants trace):
```bash
bash ${CLAUDE_PLUGIN_ROOT}/scripts/run-tlc.sh --trace
```

**For full output** (only if user explicitly requests):
```bash
bash ${CLAUDE_PLUGIN_ROOT}/scripts/run-dafny-verify.sh --full
bash ${CLAUDE_PLUGIN_ROOT}/scripts/run-tlc.sh --full
```

## Interpreting Dafny Results

The `--errors` output is a JSON array. For each error:

| Error Type | Plain Language | Common Fix |
|------------|----------------|------------|
| `precondition` | Method called without ensuring its requirements | Add assertions before call or strengthen caller's preconditions |
| `postcondition` | Method body doesn't guarantee its promises | Fix implementation or weaken postcondition |
| `invariant` | State constraint could be violated | Fix method body or add missing invariant |
| `assertion` | Explicit assertion could be false | Add intermediate assertions to guide prover |
| `termination` | Loop or recursion might not terminate | Add explicit `decreases` clause |
| `syntax` | Code doesn't parse | Fix syntax error (often predicate return types) |

For detailed error explanations, see `skills/dafny-patterns/references/common-errors.md`.

## Interpreting TLC Results

The `--trace` output shows an abbreviated counterexample (first 5 states + last).

| Violation Type | Meaning | Common Fix |
|----------------|---------|------------|
| `invariant` | Safety property fails in some reachable state | Strengthen action guards or fix invariant |
| `temporal` | Liveness property fails (something doesn't eventually happen) | Add fairness conditions or fix spec |
| `deadlock` | System gets stuck with no enabled actions | Add actions or fix guards |

For detailed TLC guidance, see `skills/tla-patterns/references/tlc-guide.md`.

## Suggest Fixes

For each failure, provide:

1. **Plain language explanation** of what went wrong
2. **Source location** (file:line from error output)
3. **Proposed fix options**:
   - For Dafny: strengthen precondition, weaken postcondition, add invariant, fix implementation
   - For TLC: add fairness, strengthen guards, add action

Ask user which approach to take before making changes.

## Cross-Model Consistency

After individual verification succeeds, check cross-model consistency:

1. **Every TLA+ action should preserve Dafny invariants**
   - Simulate: Can TLA+ action produce state violating Dafny invariant?

2. **Every Dafny method should have TLA+ counterpart**
   - Check: Does each Dafny method have corresponding TLA+ action?

3. **Type constraints align**
   - Check: Do Dafny refinement types match TLA+ type invariants?

Report any inconsistencies found.

## Verification Summary

After all checks, provide summary:

```
Verification Results
====================
Dafny (Structure): [PASSED/FAILED]
  - Methods verified: N
  - Issues: [list if any]

TLC (Behavior): [PASSED/FAILED]
  - States explored: N (distinct: M)
  - Issues: [list if any]

Cross-Model: [CONSISTENT/INCONSISTENT]
  - Issues: [list if any]

Next Steps:
- [If passed] Ready for /generate to create implementation
- [If failed] Fix issues above, then re-run /verify
```

## Interactive Resolution

If verification fails, offer to help resolve:

**Question**: "Would you like help resolving these issues?"
**Options**:
- Fix automatically - Apply suggested fixes
- Explain more - Get detailed explanation of failures
- Modify assertion - Change the underlying assertion
- Skip for now - Mark issue for later

## Available Scripts Reference

| Script | Purpose |
|--------|---------|
| `verify-all.sh --summary` | Quick pass/fail for both tools |
| `verify-all.sh --detailed` | Full JSON breakdown |
| `run-dafny-verify.sh --summary` | Dafny summary only |
| `run-dafny-verify.sh --errors` | Dafny errors as JSON array |
| `run-dafny-verify.sh --full` | Complete Dafny output |
| `run-tlc.sh --summary` | TLC summary only |
| `run-tlc.sh --trace` | Abbreviated counterexample |
| `run-tlc.sh --trace-full` | Complete counterexample |
| `run-tlc.sh --violated` | List of violated properties |
