---
name: code-generation
description: This skill should be used when generating code from verified specifications, extracting code from Dafny, creating TypeScript implementations from specs, generating Effect Schemas, writing spec-guided code, or when the user asks "generate code", "extract from Dafny", "create implementation", "generate TypeScript", "write the code", "create Effect Schemas from spec", "compile specs to code", "implement the domain logic", or "generate tests from contracts".
version: 0.1.0
---

# Code Generation

Generate correct implementations from verified Dafny and TLA+ specifications using [Effect](https://effect.website/docs).

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
3. Generate Effect Schemas from refinement types
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
import { Schema, Effect, Data } from 'effect';

/**
 * @generated
 * @source-assertion A-047: "Can only withdraw if sufficient funds"
 * @source-spec specs/dafny/account.dfy:45-52
 * @verified 2024-01-15T10:30:00Z
 */
const WithdrawInput = Schema.Struct({
  amount: Schema.Number.pipe(Schema.positive())
});

class InsufficientFunds extends Data.TaggedError('InsufficientFunds')<{
  readonly balance: number;
  readonly requested: number;
}> {}

const withdraw = (
  account: Account,
  input: typeof WithdrawInput.Type
): Effect.Effect<{ newBalance: number }, InsufficientFunds> =>
  Effect.gen(function* () {
    const { amount } = input;

    // Precondition: amount <= balance
    if (amount > account.balance) {
      return yield* Effect.fail(
        new InsufficientFunds({ balance: account.balance, requested: amount })
      );
    }

    // Postcondition: balance == old(balance) - amount
    return { newBalance: account.balance - amount };
  });
```

### Effect Schema Generation

Map Dafny types to Effect Schema:

| Dafny | Effect Schema |
|-------|--------------|
| `type Age = x: int \| x > 0` | `Schema.Number.pipe(Schema.int(), Schema.positive())` |
| `type Price = x: real \| x >= 0` | `Schema.Number.pipe(Schema.nonNegative())` |
| `type NonEmpty = s: string \| \|s\| > 0` | `Schema.String.pipe(Schema.minLength(1))` |
| `datatype Status = A \| B \| C` | `Schema.Literal('A', 'B', 'C')` |

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
import { Schema } from 'effect';

// From: class Account { var balance: int; ghost predicate Valid() { balance >= 0 } }
interface Account {
  id: string;
  balance: number;
}

const AccountSchema = Schema.Struct({
  id: Schema.String.pipe(Schema.uuid()),
  balance: Schema.Number.pipe(Schema.int(), Schema.nonNegative())
});

type Account = typeof AccountSchema.Type;
```

### Validation Layer

**From Dafny preconditions:**

```typescript
import { Schema, Effect, Data } from 'effect';

// From: requires amount > 0; requires amount <= balance
class InvalidAmount extends Data.TaggedError('InvalidAmount')<{
  readonly amount: number;
}> {}

class InsufficientFunds extends Data.TaggedError('InsufficientFunds')<{
  readonly balance: number;
  readonly requested: number;
}> {}

const validateWithdraw = (
  account: Account,
  amount: number
): Effect.Effect<void, InvalidAmount | InsufficientFunds> =>
  Effect.gen(function* () {
    if (amount <= 0) {
      return yield* Effect.fail(new InvalidAmount({ amount }));
    }
    if (amount > account.balance) {
      return yield* Effect.fail(
        new InsufficientFunds({ balance: account.balance, requested: amount })
      );
    }
  });
```

### Domain Logic Layer

**From Dafny method bodies:**

```typescript
// Core business logic - may be extracted or generated
const applyWithdraw = (account: Account, amount: number): Account => ({
  ...account,
  balance: account.balance - amount
});

const withdraw = (
  account: Account,
  amount: number
): Effect.Effect<Account, InvalidAmount | InsufficientFunds> =>
  Effect.gen(function* () {
    yield* validateWithdraw(account, amount);
    return applyWithdraw(account, amount);
  });
```

### State Machine Layer

**From TLA+ actions:**

```typescript
import { Schema } from 'effect';

// From TLA+: VARIABLES orderState; Next == Confirm \/ Ship \/ Cancel
// src/state/order.ts
/**
 * @generated
 * @source-spec specs/tla/behavior.tla:20-45
 */
const OrderState = Schema.Literal(
  'pending',
  'confirmed',
  'shipped',
  'delivered',
  'cancelled'
);
type OrderState = typeof OrderState.Type;

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

function transition<T extends { state: OrderState }>(
  entity: T,
  to: OrderState
): T | null {
  if (!canTransition(entity.state, to)) return null;
  return { ...entity, state: to };
}
```

## Test Generation

Generate tests from specs:

### Property-Based Tests (from Dafny)

```typescript
import { fc } from '@fast-check/vitest';
import { Effect } from 'effect';

// From Dafny postcondition
test.prop([fc.integer({ min: 1, max: 1000 })])('withdraw decreases balance', async (amount) => {
  const account = { id: '1', balance: 1000 };
  const result = await Effect.runPromiseExit(withdraw(account, amount));
  if (result._tag === 'Success') {
    expect(result.value.balance).toBe(account.balance - amount);
  }
});

// From Dafny invariant
test.prop([fc.integer()])('balance never negative', async (amount) => {
  const account = { id: '1', balance: 100 };
  const result = await Effect.runPromiseExit(withdraw(account, amount));
  if (result._tag === 'Success') {
    expect(result.value.balance).toBeGreaterThanOrEqual(0);
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
│   └── schemas.ts        # Effect Schemas
└── src/
    ├── services/         # Business logic (uses generated)
    └── api/              # API layer (uses generated)
```

## Additional Resources

### Example Files
- **`examples/account-generated.ts`** - Complete generated TypeScript from Dafny/TLA+ specs

### Effect Schema Mapping Quick Reference

| Dafny | Effect Schema |
|-------|--------------|
| `type X = x: int \| x > 0` | `Schema.Number.pipe(Schema.int(), Schema.positive())` |
| `type X = x: int \| x >= 0` | `Schema.Number.pipe(Schema.int(), Schema.nonNegative())` |
| `type X = x: int \| a <= x <= b` | `Schema.Number.pipe(Schema.int(), Schema.between(a, b))` |
| `type X = s: string \| \|s\| > 0` | `Schema.String.pipe(Schema.minLength(1))` |
| `type X = s: string \| \|s\| <= n` | `Schema.String.pipe(Schema.maxLength(n))` |
| `datatype X = A \| B \| C` | `Schema.Literal('A', 'B', 'C')` |
| `class C { var x: int }` | `Schema.Struct({ x: Schema.Number.pipe(Schema.int()) })` |

### External References

- **Effect Documentation**: https://effect.website/docs
- **Effect Schema**: https://effect.website/docs/schema/introduction
- **Effect Schema Filters**: https://effect.website/docs/schema/filters
- **Effect Error Handling**: https://effect.website/docs/error-management/expected-errors
