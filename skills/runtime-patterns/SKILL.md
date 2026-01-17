---
description: This skill provides TypeScript runtime validation patterns for spec-driven development. Use when generating runtime validators from Dafny specs, implementing Zod schemas from refinement types, creating branded types, using Effect for error handling, or implementing runtime contract checking. Triggers on "runtime validation", "Zod schema from spec", "branded types", "Effect error handling", "contract checking".
---

# Runtime Validation Patterns

Implement runtime validation in TypeScript that mirrors Dafny formal specifications.

## Core Principle

Dafny provides compile-time verification. TypeScript needs runtime checks at system boundaries (API inputs, external data, user input). These patterns bridge the gap.

## Zod Schemas from Dafny Types

### Refinement Types → Zod

Dafny refinement types become Zod schemas with constraints:

```dafny
// Dafny
type Age = x: int | 0 < x < 150
type NonEmptyString = s: string | |s| > 0
type Percentage = x: real | 0.0 <= x <= 100.0
```

```typescript
// TypeScript + Zod
import { z } from 'zod';

export const AgeSchema = z.number().int().min(1).max(149);
export const NonEmptyStringSchema = z.string().min(1);
export const PercentageSchema = z.number().min(0).max(100);
```

### Class Invariants → Object Schemas

Dafny class invariants become Zod object refinements:

```dafny
// Dafny
class Account {
  var balance: int
  var overdraftLimit: int
  ghost predicate Valid() {
    balance >= -overdraftLimit && overdraftLimit >= 0
  }
}
```

```typescript
// TypeScript + Zod
export const AccountSchema = z.object({
  balance: z.number().int(),
  overdraftLimit: z.number().int().nonnegative()
}).refine(
  data => data.balance >= -data.overdraftLimit,
  { message: "Balance cannot exceed overdraft limit" }
);
```

## Branded Types for Refinement Types

Use branded types when you need compile-time distinction:

```typescript
// Branded type pattern
type Brand<T, B> = T & { readonly __brand: B };

type PositiveInt = Brand<number, 'PositiveInt'>;
type NonEmptyString = Brand<string, 'NonEmptyString'>;
type AccountId = Brand<string, 'AccountId'>;

// Smart constructors
function positiveInt(n: number): PositiveInt | null {
  return n > 0 && Number.isInteger(n) ? n as PositiveInt : null;
}

function nonEmptyString(s: string): NonEmptyString | null {
  return s.length > 0 ? s as NonEmptyString : null;
}

// Usage - compiler prevents mixing branded types
function withdraw(accountId: AccountId, amount: PositiveInt): void {
  // amount is guaranteed positive at compile time
}
```

### Zod + Branded Types Combined

```typescript
import { z } from 'zod';

// Define branded type
type PositiveInt = number & { readonly __brand: 'PositiveInt' };

// Zod schema that produces branded type
const PositiveIntSchema = z.number().int().positive().transform(
  (n): PositiveInt => n as PositiveInt
);

// Parse returns branded type
const amount = PositiveIntSchema.parse(100); // PositiveInt
```

## Effect for Structured Errors

Use Effect for operations that can fail in multiple ways:

### Discriminated Union Errors

```typescript
// Error types matching Dafny precondition violations
type WithdrawError =
  | { _tag: 'InvalidAmount'; amount: number }
  | { _tag: 'InsufficientFunds'; balance: number; requested: number }
  | { _tag: 'AccountNotFound'; accountId: string };

// Result type
type WithdrawResult<T> =
  | { success: true; value: T }
  | { success: false; error: WithdrawError };

function withdraw(
  account: Account,
  amount: number
): WithdrawResult<Account> {
  if (amount <= 0) {
    return { success: false, error: { _tag: 'InvalidAmount', amount } };
  }
  if (amount > account.balance) {
    return {
      success: false,
      error: {
        _tag: 'InsufficientFunds',
        balance: account.balance,
        requested: amount
      }
    };
  }
  return {
    success: true,
    value: { ...account, balance: account.balance - amount }
  };
}
```

### With Effect Library

```typescript
import { Effect, Either } from 'effect';

class InvalidAmount {
  readonly _tag = 'InvalidAmount';
  constructor(readonly amount: number) {}
}

class InsufficientFunds {
  readonly _tag = 'InsufficientFunds';
  constructor(readonly balance: number, readonly requested: number) {}
}

type WithdrawError = InvalidAmount | InsufficientFunds;

const withdraw = (
  account: Account,
  amount: number
): Effect.Effect<Account, WithdrawError> =>
  Effect.gen(function* () {
    if (amount <= 0) {
      return yield* Effect.fail(new InvalidAmount(amount));
    }
    if (amount > account.balance) {
      return yield* Effect.fail(
        new InsufficientFunds(account.balance, amount)
      );
    }
    return { ...account, balance: account.balance - amount };
  });
```

## Runtime Contract Checking

Wrap functions with contract checks for development:

### Basic Contract Wrapper

```typescript
interface Contract<T extends (...args: any[]) => any> {
  pre?: (...args: Parameters<T>) => boolean;
  post?: (result: ReturnType<T>, ...args: Parameters<T>) => boolean;
  assertionId: string;
}

function withContract<T extends (...args: any[]) => any>(
  fn: T,
  contract: Contract<T>
): T {
  return ((...args: Parameters<T>): ReturnType<T> => {
    // Check precondition
    if (contract.pre && !contract.pre(...args)) {
      throw new ContractViolation(
        contract.assertionId,
        'precondition',
        args
      );
    }

    const result = fn(...args);

    // Check postcondition
    if (contract.post && !contract.post(result, ...args)) {
      throw new ContractViolation(
        contract.assertionId,
        'postcondition',
        { args, result }
      );
    }

    return result;
  }) as T;
}

class ContractViolation extends Error {
  constructor(
    public assertionId: string,
    public type: 'precondition' | 'postcondition',
    public context: unknown
  ) {
    super(`Contract violation [${assertionId}]: ${type} failed`);
  }
}
```

### Usage with Generated Code

```typescript
/**
 * @source-assertion A-001: "Amount must be positive"
 * @source-assertion A-002: "Balance never negative"
 */
const withdrawWithContracts = withContract(withdraw, {
  assertionId: 'A-001,A-002',
  pre: (account, amount) => amount > 0 && amount <= account.balance,
  post: (result, account, amount) =>
    !result.success || result.value.balance >= 0
});
```

### Development-Only Contracts

```typescript
const IS_DEV = process.env.NODE_ENV !== 'production';

function maybeWithContract<T extends (...args: any[]) => any>(
  fn: T,
  contract: Contract<T>
): T {
  return IS_DEV ? withContract(fn, contract) : fn;
}
```

## State Machine Runtime Enforcement

From TLA+ state machines, generate runtime-enforced transitions:

```typescript
// Generated from TLA+ spec
type OrderState = 'pending' | 'confirmed' | 'shipped' | 'delivered' | 'cancelled';

const transitions: Record<OrderState, readonly OrderState[]> = {
  pending: ['confirmed', 'cancelled'],
  confirmed: ['shipped', 'cancelled'],
  shipped: ['delivered'],
  delivered: [],
  cancelled: []
} as const;

class StateMachine<S extends string> {
  constructor(
    private state: S,
    private validTransitions: Record<S, readonly S[]>
  ) {}

  transition(to: S): boolean {
    if (!this.validTransitions[this.state].includes(to)) {
      console.error(
        `Invalid transition: ${this.state} → ${to}. ` +
        `Valid: ${this.validTransitions[this.state].join(', ')}`
      );
      return false;
    }
    this.state = to;
    return true;
  }

  get current(): S {
    return this.state;
  }
}

// Usage
const order = new StateMachine<OrderState>('pending', transitions);
order.transition('confirmed'); // true
order.transition('shipped');   // true
order.transition('pending');   // false - logged error
```

## Validation at Boundaries

Apply runtime validation only at system boundaries:

```typescript
// API boundary - validate incoming data
app.post('/withdraw', async (c) => {
  // Parse and validate at boundary
  const input = WithdrawInputSchema.safeParse(await c.req.json());

  if (!input.success) {
    return c.json({ error: input.error.format() }, 400);
  }

  // Inside boundary - types are trusted
  const result = withdraw(account, input.data.amount);

  return c.json(result);
});

// Internal code - no runtime validation needed
function calculateInterest(account: Account): number {
  // Account is already validated - trust the types
  return account.balance * 0.05;
}
```

## Examples

See `examples/` for complete implementations:
- `validated-account.ts` - Full account with all patterns
- `order-state-machine.ts` - TLA+-derived state machine
- `api-validation.ts` - Hono API with Zod validation
