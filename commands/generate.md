---
description: Generate implementation code from verified specifications
argument-hint: [layer]
allowed-tools: Read, Write, Edit, Bash, AskUserQuestion
model: sonnet
---

# Code Generation

Generate implementation code from verified Dafny and TLA+ specifications.

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
- `types` - Type definitions and Zod schemas
- `validation` - Input validators from preconditions
- `domain` - Core business logic
- `state` - State machines from TLA+
- `api` - API layer (routes, handlers)
- `tests` - Test suites from contracts

If no argument, generate all layers in order.

## Verified Extraction (Mode 1)

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
import { z } from 'zod';

export const AgeSchema = z.number().int().min(1).max(149);
export type Age = z.infer<typeof AgeSchema>;
```

Add traceability comments linking to source assertion.

### Validation Layer

Read Dafny preconditions (requires clauses).
Generate to `src/validation/`:

```typescript
// From Dafny: requires amount > 0; requires amount <= balance
// src/validation/withdraw.ts
/**
 * @generated
 * @source-assertion A-052
 * @source-spec specs/dafny/account.dfy:45-48
 */
export const validateWithdraw = (account: Account, amount: number) => {
  if (amount <= 0) {
    return { valid: false, error: 'INVALID_AMOUNT' as const };
  }
  if (amount > account.balance) {
    return { valid: false, error: 'INSUFFICIENT_FUNDS' as const };
  }
  return { valid: true } as const;
};
```

### Domain Logic Layer

Read Dafny method bodies and postconditions.
Generate to `src/domain/`:

```typescript
// From Dafny: ensures balance == old(balance) - amount
// src/domain/account.ts
/**
 * @generated
 * @source-assertion A-053
 * @source-spec specs/dafny/account.dfy:50-55
 */
export function withdraw(account: Account, amount: number): WithdrawResult {
  const validation = validateWithdraw(account, amount);
  if (!validation.valid) {
    return { success: false, error: validation.error };
  }
  return {
    success: true,
    account: { ...account, balance: account.balance - amount }
  };
}
```

### State Machine Layer

Read TLA+ actions and state transitions.
Generate to `src/state/`:

```typescript
// From TLA+: VARIABLES orderState; Next == Confirm \/ Ship \/ Cancel
// src/state/order.ts
/**
 * @generated
 * @source-spec specs/tla/behavior.tla:20-45
 */
export type OrderState = 'pending' | 'confirmed' | 'shipped' | 'delivered' | 'cancelled';

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
import { zValidator } from '@hono/zod-validator';
import { withdraw } from '../domain/account';
import { WithdrawInputSchema } from '../types/account';

export const accountRoutes = new Hono()
  .post('/withdraw', zValidator('json', WithdrawInputSchema), async (c) => {
    const input = c.req.valid('json');
    const account = await getAccount(input.accountId);
    const result = withdraw(account, input.amount);
    if (!result.success) {
      return c.json({ error: result.error }, 400);
    }
    await saveAccount(result.account);
    return c.json({ balance: result.account.balance });
  });
```

### Test Generation Layer

Read Dafny contracts for property-based tests.
Read TLA+ traces for integration tests.
Generate to `tests/`:

```typescript
// tests/account.test.ts
import { test, expect } from 'vitest';
import { fc } from '@fast-check/vitest';
import { withdraw } from '../src/domain/account';

// Property from Dafny postcondition
test.prop([fc.integer({ min: 1, max: 1000 })])('withdraw decreases balance correctly', (amount) => {
  const account = { id: '1', balance: 1000 };
  const result = withdraw(account, amount);
  if (result.success) {
    expect(result.account.balance).toBe(1000 - amount);
  }
});

// Invariant from Dafny
test.prop([fc.integer()])('balance never negative after withdraw', (amount) => {
  const account = { id: '1', balance: 100 };
  const result = withdraw(account, amount);
  if (result.success) {
    expect(result.account.balance).toBeGreaterThanOrEqual(0);
  }
});
```

## Contract-First Generation (Mode 3)

Generate interfaces only, with TODO markers for implementation.

```typescript
// src/domain/account.ts
/**
 * @contract
 * @requires amount > 0
 * @requires amount <= account.balance
 * @ensures result.success implies new balance = old balance - amount
 */
export function withdraw(account: Account, amount: number): WithdrawResult {
  // TODO: Implement according to contract above
  throw new Error('Not implemented');
}
```

## Output Structure

Create/update project structure:

```
src/
├── types/           # Zod schemas and types
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
