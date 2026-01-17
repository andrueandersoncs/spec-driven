---
description: Run tests and generate assertion coverage report
argument-hint: [watch|coverage|specific-test]
allowed-tools: Read, Bash, Glob, Write
model: sonnet
---

# Test Execution with Assertion Coverage

Run generated tests and map results back to source assertions.

## Prerequisites

Check that the project is scaffolded:
- `package.json` exists
- `node_modules/` exists (or run `bun install`)
- `tests/` directory with test files

If not scaffolded, instruct user to run `/scaffold` first.

## Test Execution

### Standard Run

```bash
bun test 2>&1
```

### Watch Mode

If `$ARGUMENTS` contains "watch":
```bash
bun test --watch
```

### Coverage Mode

If `$ARGUMENTS` contains "coverage":
```bash
bun test --coverage
```

### Specific Test

If `$ARGUMENTS` contains a test file pattern:
```bash
bun test $ARGUMENTS
```

## Assertion Coverage Analysis

After tests complete, analyze coverage against assertions.

### 1. Parse Test Results

Extract from Bun test output:
- Test file names
- Test descriptions
- Pass/fail status
- Error messages for failures

### 2. Extract Assertion Links

Read each test file and extract `@source-assertion` comments:

```typescript
// tests/account.test.ts
/**
 * @source-assertion A-001: "Account balance never negative"
 * @source-assertion A-002: "Withdraw requires sufficient funds"
 */
```

Build a map: `test file → [assertion IDs]`

### 3. Load Assertion Manifest

Read `specs/assertions.json` to get full assertion list:

```json
{
  "assertions": [
    { "id": "A-001", "text": "Account balance never negative", "status": "confirmed" },
    { "id": "A-002", "text": "Withdraw requires sufficient funds", "status": "confirmed" },
    { "id": "A-003", "text": "Transfer is atomic", "status": "confirmed" }
  ]
}
```

### 4. Compute Coverage

For each assertion:
- Count tests that reference it
- Count passing vs failing tests
- Identify assertions with no tests

### 5. Generate Report

```
Assertion Coverage Report
=========================

Assertions Tested: 2/3 (67%)

✅ A-001: "Account balance never negative"
   └─ 3 tests (all passing)
   └─ tests/account.test.ts:15, :28, :45

✅ A-002: "Withdraw requires sufficient funds"
   └─ 2 tests (all passing)
   └─ tests/account.test.ts:52, :67

❌ A-003: "Transfer is atomic"
   └─ 0 tests
   └─ RECOMMENDATION: Add integration test for concurrent transfers

─────────────────────────────────
Test Summary: 5 passed, 0 failed
Assertion Coverage: 67% (2/3)
```

## Failure Analysis

When tests fail, map failures back to assertions:

### 1. Parse Error Message

Extract:
- Test name
- Assertion that failed
- Expected vs actual values
- Stack trace location

### 2. Link to Source Spec

From the test file's `@source-assertion` comment, find:
- The assertion text
- The source spec file and line range
- The Dafny/TLA+ constraint

### 3. Explain Failure

```
Test Failure Analysis
=====================

FAILED: "balance never negative after withdraw"
  tests/account.test.ts:28

Linked Assertion: A-001
  "Account balance never negative"
  Source: specs/dafny/structure.dfy:12-15

  invariant Valid() { balance >= 0 }

What went wrong:
  The test generated a case where:
  - Initial balance: 50
  - Withdraw amount: 100
  - Result balance: -50 (violated invariant)

Possible causes:
  1. Generated validation doesn't check insufficient funds
  2. Test is using invalid input (property test found edge case)
  3. Spec is incomplete (missing precondition)

Recommended action:
  Check src/validation/account.ts line 18 - ensure amount <= balance check
```

## Integration with Formal Verification

### Cross-Check with Dafny/TLC

If tests fail but verification passed:
- The generated code may not correctly implement the spec
- Re-run `/generate` to regenerate
- Check traceability links for discrepancies

If both tests and verification fail:
- The spec itself has issues
- Run `/resolve-conflict` to fix

### Property Test → Formal Proof Gap

Property tests (fast-check) are statistical sampling.
Formal verification (Dafny) is mathematical proof.

If property tests pass but you want higher assurance:
- Review the Dafny verification output
- Consider adding more specific assertions
- Run TLC with larger state bounds

## Continuous Testing

### Watch Mode Integration

When running in watch mode:
1. Tests re-run on file changes
2. Assertion coverage updates live
3. Failures are immediately linked to specs

### CI Integration

Generate assertion coverage for CI:

```bash
bun test --coverage > test-output.txt
# Parse and generate coverage badge/report
```

## Report Files

Optionally generate persistent reports:

### `coverage/assertion-coverage.json`

```json
{
  "timestamp": "2024-01-15T10:30:00Z",
  "assertions": {
    "A-001": { "tests": 3, "passing": 3, "failing": 0 },
    "A-002": { "tests": 2, "passing": 2, "failing": 0 },
    "A-003": { "tests": 0, "passing": 0, "failing": 0 }
  },
  "coverage": 0.67,
  "totalTests": 5,
  "passingTests": 5,
  "failingTests": 0
}
```

### `coverage/assertion-coverage.md`

Human-readable markdown report for documentation.

## Summary Output

After test run:

```
Test Results
============
Runtime: 1.23s
Tests: 5 passed, 0 failed

Assertion Coverage
==================
Covered: 2/3 assertions (67%)
  ✅ A-001 (3 tests)
  ✅ A-002 (2 tests)
  ❌ A-003 (no tests)

Next Steps:
  • Add tests for A-003: "Transfer is atomic"
  • Run /verify to ensure formal proofs still hold
  • Run /dev to start development server
```
