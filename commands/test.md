---
description: Run tests and generate assertion coverage report
argument-hint: [watch|coverage|specific-test]
allowed-tools: Read, Bash, Glob, Write
model: sonnet
---

# Test Execution with Assertion Coverage

Run generated tests and map results back to source assertions.

## Prerequisites Check

First, verify the project is properly scaffolded:

```bash
bash ${CLAUDE_PLUGIN_ROOT}/scripts/check-scaffolded.sh --json
```

**If status is "not_scaffolded"**: Instruct user to run `/scaffold` first.

**If status is "needs_install"**: Run `bun install` before proceeding.

**If status is "ready"**: Proceed with test execution.

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

## Progressive Disclosure for Test Failures

When tests fail, use progressive disclosure to help users focus on what matters.

### Step 1: Show Summary First

Parse test output to extract:
- Total tests run
- Tests passed
- Tests failed
- Test files with failures

Present a concise summary:
```
Test Results: 45 passed, 3 failed (2 files)
```

### Step 2: Ask User for Detail Level

**Question**: "3 tests failed. How would you like to see the failures?"
**Options**:
- Show failed test names and assertions (recommended)
- Show first failure with full stack trace
- Show all failures with stack traces
- Skip to assertion coverage report

### Step 3: Progressive Detail

Based on user choice, show appropriate level of detail. Avoid dumping full stack traces unless explicitly requested.

## Assertion Coverage Analysis

After tests complete, analyze coverage against assertions.

### 1. Extract Assertion Links from Test Files

Search test files for `@source-assertion` comments:

```bash
grep -r "@source-assertion" tests/ 2>/dev/null || echo "No assertion links found"
```

Build a map: `test file → [assertion IDs]`

### 2. Load Assertion Manifest

Read `specs/assertions.json` to get full assertion list.

Use the validation script to ensure manifest is valid:
```bash
bash ${CLAUDE_PLUGIN_ROOT}/scripts/validate-assertions.sh specs/assertions.json
```

### 3. Compute Coverage

For each assertion:
- Count tests that reference it
- Count passing vs failing tests
- Identify assertions with no tests

### 4. Generate Report

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

## Failure Analysis with Progressive Disclosure

When tests fail, map failures back to assertions.

### Step 1: Identify Failed Test

Extract from test output:
- Test name
- Test file and line
- Error message (first line only initially)

### Step 2: Link to Source Spec

From the test file's `@source-assertion` comment, find:
- The assertion text from assertions.json
- The source spec file and line range

### Step 3: Explain Failure (Concise First)

```
FAILED: "balance never negative after withdraw"
  └─ tests/account.test.ts:28
  └─ Linked to: A-001 (specs/dafny/structure.dfy:12-15)
  └─ Error: Expected balance >= 0, got -50
```

### Step 4: Offer More Detail

**Question**: "Would you like more details about this failure?"
**Options**:
- Show the full stack trace
- Show the relevant spec code
- Show the test code
- Try to fix automatically

## Integration with Formal Verification

### Cross-Check with Dafny/TLC

If tests fail but verification passed:
- The generated code may not correctly implement the spec
- Suggest re-running `/generate` to regenerate
- Check traceability links for discrepancies

If both tests and verification fail:
- The spec itself has issues
- Suggest running `/resolve-conflict` to fix

### Property Test → Formal Proof Gap

Property tests (fast-check) are statistical sampling.
Formal verification (Dafny) is mathematical proof.

If property tests pass but you want higher assurance:
- Review the Dafny verification output
- Consider adding more specific assertions
- Run TLC with larger state bounds

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

## Available Scripts Reference

| Script | Purpose |
|--------|---------|
| `check-scaffolded.sh` | Verify project is ready for testing |
| `check-scaffolded.sh --json` | JSON status of scaffold components |
| `validate-assertions.sh` | Validate assertions.json schema |
