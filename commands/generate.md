---
description: Generate implementation code from verified specifications
argument-hint: [layer]
allowed-tools: Read, Write, Edit, Bash, AskUserQuestion
model: sonnet
---

# Code Generation

Generate implementation code from verified Dafny and TLA+ specifications using [Effect](https://effect.website/docs).

## Prerequisites

Check verification status in `specs/assertions.json`:
- All assertions should be "confirmed"
- Specs should have passed verification (run `/verify` if not done)

If verification not run or failed, warn user and suggest running `/verify` first.

## Generation Modes

Determine generation mode based on target:

**Question**: "How should code be generated?"
**Options**:
- Verified Extraction (Recommended) - Compile Dafny directly to JavaScript
- Spec-Guided Generation - Generate idiomatic TypeScript from specs
- Contract-First - Generate interfaces only, implement manually

## Layer Selection

If $ARGUMENTS specifies a layer, generate only that layer:
- `types` - Type definitions and Effect Schemas
- `validation` - Input validators from preconditions
- `domain` - Core business logic
- `state` - State machines from TLA+
- `api` - API layer (routes, handlers)
- `tests` - Test suites from contracts

If no argument, generate all layers in order.

## Verified Extraction (Mode 1)

Dafny can compile verified code directly to multiple target languages. See [Compilation](https://dafny.org/latest/DafnyRef/DafnyRef#sec-compilation) in the Dafny Reference Manual for full details on supported targets and options.

### Extract from Dafny

```bash
# Compile Dafny to JavaScript
dafny build --target:js specs/dafny/structure.dfy -o generated/structure.js
```

### Generate Type Declarations

Create `generated/structure.d.ts` from Dafny source:
- Map Dafny classes to TypeScript interfaces
- Map Dafny methods to function signatures
- Map refinement types to branded types or validation

### Create Glue Code

Generate wrapper in `src/lib/verified.ts`:
- Import from generated JavaScript
- Add TypeScript types
- Wrap for ergonomic use

## Spec-Guided Generation (Mode 2)

### Types & Schemas Layer

Read Dafny classes and refinement types.
Generate to `src/types/`:

```typescript
// From Dafny: type Age = x: int | 0 < x < 150
// src/types/age.ts
import { Schema } from 'effect';

export const AgeSchema = Schema.Number.pipe(
  Schema.int(),
  Schema.greaterThan(0),
  Schema.lessThan(150)
);
export type Age = typeof AgeSchema.Type;
```

Add traceability comments linking to source assertion.

### Validation Layer

Read Dafny preconditions (requires clauses).
Generate to `src/validation/`:

```typescript
// From Dafny: requires amount > 0; requires amount <= balance
// src/validation/withdraw.ts
import { Effect, Data } from 'effect';

/**
 * @generated
 * @source-assertion A-052
 * @source-spec specs/dafny/account.dfy:45-48
 */
class InvalidAmount extends Data.TaggedError('InvalidAmount')<{
  readonly amount: number;
}> {}

class InsufficientFunds extends Data.TaggedError('InsufficientFunds')<{
  readonly balance: number;
  readonly requested: number;
}> {}

export const validateWithdraw = (
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

Read Dafny method bodies and postconditions.
Generate to `src/domain/`:

```typescript
// From Dafny: ensures balance == old(balance) - amount
// src/domain/account.ts
import { Effect } from 'effect';

/**
 * @generated
 * @source-assertion A-053
 * @source-spec specs/dafny/account.dfy:50-55
 */
export const withdraw = (
  account: Account,
  amount: number
): Effect.Effect<Account, InvalidAmount | InsufficientFunds> =>
  Effect.gen(function* () {
    yield* validateWithdraw(account, amount);
    return {
      ...account,
      balance: account.balance - amount
    };
  });
```

### State Machine Layer

Read TLA+ actions and state transitions.
Generate to `src/state/`:

```typescript
// From TLA+: VARIABLES orderState; Next == Confirm \/ Ship \/ Cancel
// src/state/order.ts
import { Schema } from 'effect';

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

export const orderTransitions: Record<OrderState, OrderState[]> = {
  pending: ['confirmed', 'cancelled'],
  confirmed: ['shipped', 'cancelled'],
  shipped: ['delivered'],
  delivered: [],
  cancelled: []
};

export function canTransition(from: OrderState, to: OrderState): boolean {
  return orderTransitions[from].includes(to);
}

export function transition(order: Order, to: OrderState): Order | null {
  if (!canTransition(order.state, to)) return null;
  return { ...order, state: to };
}
```

### API Layer

Generate API handlers based on domain operations.
Generate to `src/api/`:

```typescript
// src/api/account.ts
import { Hono } from 'hono';
import { Schema, Effect, Either } from 'effect';
import { withdraw } from '../domain/account';
import { WithdrawInputSchema } from '../types/account';

export const accountRoutes = new Hono()
  .post('/withdraw', async (c) => {
    const json = await c.req.json();
    const parseResult = Schema.decodeUnknownEither(WithdrawInputSchema)(json);

    if (Either.isLeft(parseResult)) {
      return c.json({ error: parseResult.left.message }, 400);
    }

    const input = parseResult.right;
    const account = await getAccount(input.accountId);
    const result = await Effect.runPromiseExit(withdraw(account, input.amount));

    if (result._tag === 'Failure') {
      return c.json({ error: 'Withdrawal failed' }, 400);
    }

    await saveAccount(result.value);
    return c.json({ balance: result.value.balance });
  });
```

For full Effect-native HTTP, use `@effect/platform`:

```typescript
import { HttpApiEndpoint, HttpApiGroup } from '@effect/platform';
import { Schema, Effect } from 'effect';

const WithdrawEndpoint = HttpApiEndpoint.post('withdraw', '/withdraw')
  .setPayload(WithdrawInputSchema)
  .addSuccess(Schema.Struct({ balance: Schema.Number }));

const withdrawHandler = HttpApiEndpoint.handle(WithdrawEndpoint, ({ payload }) =>
  Effect.gen(function* () {
    const account = yield* getAccount(payload.accountId);
    const updated = yield* withdraw(account, payload.amount);
    return { balance: updated.balance };
  })
);
```

### Test Generation Layer

Read Dafny contracts for property-based tests.
Read TLA+ traces for integration tests.
Generate to `tests/`:

```typescript
// tests/account.test.ts
import { test, expect } from 'vitest';
import { fc } from '@fast-check/vitest';
import { Effect } from 'effect';
import { withdraw } from '../src/domain/account';

// Property from Dafny postcondition
test.prop([fc.integer({ min: 1, max: 1000 })])('withdraw decreases balance correctly', async (amount) => {
  const account = { id: '1', balance: 1000 };
  const result = await Effect.runPromiseExit(withdraw(account, amount));
  if (result._tag === 'Success') {
    expect(result.value.balance).toBe(1000 - amount);
  }
});

// Invariant from Dafny
test.prop([fc.integer()])('balance never negative after withdraw', async (amount) => {
  const account = { id: '1', balance: 100 };
  const result = await Effect.runPromiseExit(withdraw(account, amount));
  if (result._tag === 'Success') {
    expect(result.value.balance).toBeGreaterThanOrEqual(0);
  }
});
```

## Contract-First Generation (Mode 3)

Generate interfaces only, with TODO markers for implementation.

```typescript
// src/domain/account.ts
import { Effect } from 'effect';

/**
 * @contract
 * @requires amount > 0
 * @requires amount <= account.balance
 * @ensures result.success implies new balance = old balance - amount
 */
export const withdraw = (
  account: Account,
  amount: number
): Effect.Effect<Account, WithdrawError> => {
  // TODO: Implement according to contract above
  return Effect.fail(new Error('Not implemented') as any);
};
```

## Output Structure

Create/update project structure:

```
src/
├── types/           # Effect Schemas and types
├── validation/      # Input validators
├── domain/          # Business logic
├── state/           # State machines
├── api/             # API handlers
└── lib/
    └── verified.ts  # Dafny extraction wrapper (if used)
generated/           # Dafny output (if extraction used)
tests/
├── unit/           # Property-based tests
└── integration/    # Trace-based tests
```

## Traceability

Every generated file includes:
- `@generated` marker
- `@source-assertion` linking to assertion ID
- `@source-spec` linking to formal spec file and lines
- Timestamp of generation

## Summary

Report generation results:
- Files generated/updated
- Layers completed
- Verification status of generated code
- Next steps (run tests, manual implementation for contract-first)
