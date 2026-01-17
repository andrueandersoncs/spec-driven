---
name: code-generation
description: This skill should be used when generating code from verified specifications, extracting code from Dafny, creating TypeScript implementations from specs, generating Zod schemas, writing spec-guided code, or when the user asks "generate code", "extract from Dafny", "create implementation", "generate TypeScript", "write the code", "create Zod schemas from spec", "compile specs to code", "implement the domain logic", or "generate tests from contracts".
version: 0.1.0
---

# Code Generation

Generate correct implementations from verified Dafny and TLA+ specifications.

## Generation Modes

Three approaches based on verification needs:

| Mode | Description | Use When |
|------|-------------|----------|
| **Verified Extraction** | Dafny compiles to target | Maximum correctness guarantees |
| **Spec-Guided Generation** | LLM generates constrained by spec | Need idiomatic code |
| **Contract-First** | Generate interfaces only | Complex logic, human implements |

## Verified Extraction (Preferred)

Dafny compiles directly to JavaScript for TypeScript projects.

### Extraction Workflow

```bash
# 1. Verify the spec
dafny verify specs/dafny/structure.dfy

# 2. Extract to JavaScript
dafny build --target:js specs/dafny/structure.dfy -o generated/structure.js

# 3. Generate type declarations
# (manual or LLM-assisted from Dafny source)
```

### TypeScript Integration

```typescript
// generated/structure.d.ts (from Dafny)
export interface Account {
  balance: number;
}

export function withdraw(
  account: Account,
  amount: number
): { success: boolean; account: Account };

// src/services/account.ts (glue code)
import { withdraw as dafnyWithdraw } from '../generated/structure.js';

export function withdraw(accountId: string, amount: number) {
  const account = loadAccount(accountId);
  const result = dafnyWithdraw(account, amount);
  if (result.success) {
    saveAccount(accountId, result.account);
  }
  return result;
}
```

### Extraction Limitations

- Generated code may not be idiomatic
- Unbounded integers need BigInt or bounds checking
- Sets/sequences map to arrays (performance implications)
- External library integration needs FFI boundaries

## Spec-Guided Generation

When extraction doesn't fit, generate code constrained by specs.

### Process

1. Read Dafny contract
2. Generate TypeScript implementation honoring:
   - Preconditions → runtime validation
   - Postconditions → return value guarantees
   - Invariants → state consistency
3. Generate Zod schemas from refinement types
4. Add traceability comments

### From Dafny Contract to TypeScript

**Dafny Source:**
```dafny
method Withdraw(amount: int) returns (success: bool)
  requires amount > 0
  requires amount <= balance
  ensures success ==> balance == old(balance) - amount
  ensures !success ==> balance == old(balance)
```

**Generated TypeScript:**
```typescript
/**
 * @generated
 * @source-assertion A-047: "Can only withdraw if sufficient funds"
 * @source-spec specs/dafny/account.dfy:45-52
 * @verified 2024-01-15T10:30:00Z
 */
const WithdrawInput = z.object({
  amount: z.number().positive()
});

type WithdrawResult =
  | { success: true; newBalance: number }
  | { success: false; error: 'INSUFFICIENT_FUNDS' };

function withdraw(
  account: Account,
  input: z.infer<typeof WithdrawInput>
): WithdrawResult {
  const { amount } = WithdrawInput.parse(input);

  // Precondition: amount <= balance
  if (amount > account.balance) {
    return { success: false, error: 'INSUFFICIENT_FUNDS' };
  }

  // Postcondition: balance == old(balance) - amount
  return {
    success: true,
    newBalance: account.balance - amount
  };
}
```

### Zod Schema Generation

Map Dafny types to Zod:

| Dafny | Zod |
|-------|-----|
| `type Age = x: int \| x > 0` | `z.number().int().positive()` |
| `type Price = x: real \| x >= 0` | `z.number().nonnegative()` |
| `type NonEmpty = s: string \| \|s\| > 0` | `z.string().min(1)` |
| `datatype Status = A \| B \| C` | `z.enum(['A', 'B', 'C'])` |

### Traceability Comments

Every generated artifact links to source:

```typescript
/**
 * @generated
 * @source-assertion A-052: "Withdrawal requires sufficient funds"
 * @source-assertion A-053: "Failed withdrawal doesn't change balance"
 * @source-spec specs/dafny/account.dfy:62-71
 * @verified 2024-01-15T10:30:00Z
 */
```

## Layer-by-Layer Generation

### Types & Schemas Layer

**From Dafny classes and refinement types:**

```typescript
// From: class Account { var balance: int; ghost predicate Valid() { balance >= 0 } }
interface Account {
  id: string;
  balance: number;
}

const AccountSchema = z.object({
  id: z.string().uuid(),
  balance: z.number().int().nonnegative()
});
```

### Validation Layer

**From Dafny preconditions:**

```typescript
// From: requires amount > 0; requires amount <= balance
const validateWithdraw = (account: Account, amount: number) => {
  if (amount <= 0) {
    return { valid: false, error: 'INVALID_AMOUNT' };
  }
  if (amount > account.balance) {
    return { valid: false, error: 'INSUFFICIENT_FUNDS' };
  }
  return { valid: true };
};
```

### Domain Logic Layer

**From Dafny method bodies:**

```typescript
// Core business logic - may be extracted or generated
function applyWithdraw(account: Account, amount: number): Account {
  return {
    ...account,
    balance: account.balance - amount
  };
}
```

### State Machine Layer

**From TLA+ actions:**

```typescript
// From TLA+ state machine
type OrderState = 'pending' | 'confirmed' | 'shipped' | 'delivered' | 'cancelled';

const orderTransitions: Record<OrderState, OrderState[]> = {
  pending: ['confirmed', 'cancelled'],
  confirmed: ['shipped', 'cancelled'],
  shipped: ['delivered'],
  delivered: [],
  cancelled: []
};

function canTransition(from: OrderState, to: OrderState): boolean {
  return orderTransitions[from].includes(to);
}
```

## Test Generation

Generate tests from specs:

### Property-Based Tests (from Dafny)

```typescript
import { fc } from '@fast-check/vitest';

// From Dafny postcondition
test.prop([fc.integer({ min: 1, max: 1000 })])('withdraw decreases balance', (amount) => {
  const account = { balance: 1000 };
  const result = withdraw(account, amount);
  if (result.success) {
    expect(result.newBalance).toBe(account.balance - amount);
  }
});

// From Dafny invariant
test.prop([fc.integer()])('balance never negative', (amount) => {
  const account = { balance: 100 };
  const result = withdraw(account, amount);
  if (result.success) {
    expect(result.newBalance).toBeGreaterThanOrEqual(0);
  }
});
```

### Integration Tests (from TLA+ traces)

```typescript
// From TLC model checker trace
test('order lifecycle', async () => {
  const order = await createOrder(items);
  expect(order.status).toBe('pending');

  await confirmOrder(order.id);
  expect(order.status).toBe('confirmed');

  await shipOrder(order.id);
  expect(order.status).toBe('shipped');

  await deliverOrder(order.id);
  expect(order.status).toBe('delivered');
});
```

## Incremental Regeneration

When specs change, regenerate affected code:

1. Identify changed assertions in `specs/assertions.json`
2. Find code with matching `@source-assertion` comments
3. Regenerate those specific artifacts
4. Re-run affected tests
5. Surface conflicts if tests fail

## Directory Structure

```
project/
├── specs/
│   ├── dafny/
│   │   └── structure.dfy
│   ├── tla/
│   │   └── behavior.tla
│   └── assertions.json
├── generated/
│   ├── structure.js      # Dafny extraction
│   ├── structure.d.ts    # Type declarations
│   └── schemas.ts        # Zod schemas
└── src/
    ├── services/         # Business logic (uses generated)
    └── api/              # API layer (uses generated)
```

## Additional Resources

### Example Files
- **`examples/account-generated.ts`** - Complete generated TypeScript from Dafny/TLA+ specs

### Zod Mapping Quick Reference

| Dafny | Zod |
|-------|-----|
| `type X = x: int \| x > 0` | `z.number().int().positive()` |
| `type X = x: int \| x >= 0` | `z.number().int().nonnegative()` |
| `type X = x: int \| a <= x <= b` | `z.number().int().min(a).max(b)` |
| `type X = s: string \| \|s\| > 0` | `z.string().min(1)` |
| `type X = s: string \| \|s\| <= n` | `z.string().max(n)` |
| `datatype X = A \| B \| C` | `z.enum(['A', 'B', 'C'])` |
| `class C { var x: int }` | `z.object({ x: z.number().int() })` |
