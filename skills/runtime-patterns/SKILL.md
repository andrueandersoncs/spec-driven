---
name: runtime-patterns
version: 0.1.0
description: This skill provides TypeScript runtime validation patterns for spec-driven development. Use when generating runtime validators from Dafny specs, implementing Effect Schemas from refinement types, creating branded types, using Effect for error handling, or implementing runtime contract checking. Triggers on "runtime validation", "Effect Schema from spec", "branded types", "Effect error handling", "contract checking".
---

# Runtime Validation Patterns

Implement runtime validation in TypeScript that mirrors Dafny formal specifications using [Effect](https://effect.website/docs).

## Core Principle

Dafny provides compile-time verification. TypeScript needs runtime checks at system boundaries (API inputs, external data, user input). These patterns bridge the gap using Effect Schema for validation and Effect for error handling.

## Effect Schemas from Dafny Types

### Refinement Types → Effect Schema

Dafny refinement types become Effect Schemas with constraints:

```dafny
// Dafny
type Age = x: int | 0 < x < 150
type NonEmptyString = s: string | |s| > 0
type Percentage = x: real | 0.0 <= x <= 100.0
```

```typescript
// TypeScript + Effect Schema
import { Schema } from 'effect';

export const AgeSchema = Schema.Number.pipe(
  Schema.int(),
  Schema.greaterThan(0),
  Schema.lessThan(150)
);

export const NonEmptyStringSchema = Schema.String.pipe(
  Schema.minLength(1)
);

export const PercentageSchema = Schema.Number.pipe(
  Schema.greaterThanOrEqualTo(0),
  Schema.lessThanOrEqualTo(100)
);
```

### Class Invariants → Struct Schemas with Filters

Dafny class invariants become Effect Schema structs with filters:

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
// TypeScript + Effect Schema
import { Schema } from 'effect';

export const AccountSchema = Schema.Struct({
  balance: Schema.Number.pipe(Schema.int()),
  overdraftLimit: Schema.Number.pipe(Schema.int(), Schema.nonNegative())
}).pipe(
  Schema.filter((data) =>
    data.balance >= -data.overdraftLimit
      ? true
      : 'Balance cannot exceed overdraft limit'
  )
);
```

## Branded Types for Refinement Types

Use Effect Schema branded types for compile-time distinction:

```typescript
import { Schema, Brand } from 'effect';

// Define branded types using Effect Schema
const PositiveInt = Schema.Number.pipe(
  Schema.int(),
  Schema.positive(),
  Schema.brand('PositiveInt')
);
type PositiveInt = Schema.Schema.Type<typeof PositiveInt>;

const NonEmptyString = Schema.String.pipe(
  Schema.minLength(1),
  Schema.brand('NonEmptyString')
);
type NonEmptyString = Schema.Schema.Type<typeof NonEmptyString>;

const AccountId = Schema.String.pipe(
  Schema.minLength(1),
  Schema.brand('AccountId')
);
type AccountId = Schema.Schema.Type<typeof AccountId>;

// Parse to create branded values
const accountId = Schema.decodeUnknownSync(AccountId)('acc-123');
const amount = Schema.decodeUnknownSync(PositiveInt)(100);

// Usage - compiler prevents mixing branded types
function withdraw(accountId: AccountId, amount: PositiveInt): void {
  // amount is guaranteed positive at compile time
}
```

### Combining Multiple Brands

```typescript
import { Schema } from 'effect';

// Combine multiple refinements using extend
const Integer = Schema.Int.pipe(Schema.brand('Int'));
const Positive = Schema.Positive.pipe(Schema.brand('Positive'));

// Combined branded type
const PositiveInteger = Schema.asSchema(Schema.extend(Positive, Integer));
type PositiveInteger = Schema.Schema.Type<typeof PositiveInteger>;

// Parse returns combined branded type
const amount = Schema.decodeUnknownSync(PositiveInteger)(100);
// Type: number & Brand<"Positive"> & Brand<"Int">
```

## Effect for Structured Errors

Use Effect for operations that can fail in multiple ways:

### Error Types as Tagged Classes

```typescript
import { Effect, Data } from 'effect';

// Error types matching Dafny precondition violations
class InvalidAmount extends Data.TaggedError('InvalidAmount')<{
  readonly amount: number;
}> {}

class InsufficientFunds extends Data.TaggedError('InsufficientFunds')<{
  readonly balance: number;
  readonly requested: number;
}> {}

class AccountNotFound extends Data.TaggedError('AccountNotFound')<{
  readonly accountId: string;
}> {}

type WithdrawError = InvalidAmount | InsufficientFunds | AccountNotFound;
```

### Effect-Based Domain Logic

```typescript
import { Effect } from 'effect';

const withdraw = (
  account: Account,
  amount: number
): Effect.Effect<Account, WithdrawError> =>
  Effect.gen(function* () {
    // Precondition: amount > 0
    if (amount <= 0) {
      return yield* Effect.fail(new InvalidAmount({ amount }));
    }

    // Precondition: amount <= balance
    if (amount > account.balance) {
      return yield* Effect.fail(
        new InsufficientFunds({
          balance: account.balance,
          requested: amount
        })
      );
    }

    // Postcondition: balance == old(balance) - amount
    return { ...account, balance: account.balance - amount };
  });

// Usage with comprehensive error handling
const program = Effect.gen(function* () {
  const account = { id: 'acc-1', balance: 100 };
  const result = yield* withdraw(account, 50);
  return result;
}).pipe(
  Effect.catchTags({
    InvalidAmount: (e) => Effect.succeed({ error: `Invalid amount: ${e.amount}` }),
    InsufficientFunds: (e) => Effect.succeed({ error: `Insufficient: ${e.balance} < ${e.requested}` }),
    AccountNotFound: (e) => Effect.succeed({ error: `Not found: ${e.accountId}` })
  })
);
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
import { Schema } from 'effect';

// Define input schema
const WithdrawInputSchema = Schema.Struct({
  accountId: Schema.String.pipe(Schema.minLength(1)),
  amount: Schema.Number.pipe(Schema.positive())
});

// API boundary - validate incoming data
app.post('/withdraw', async (c) => {
  // Parse and validate at boundary using Effect Schema
  const parseResult = Schema.decodeUnknownEither(WithdrawInputSchema)(
    await c.req.json()
  );

  if (parseResult._tag === 'Left') {
    return c.json({ error: parseResult.left.message }, 400);
  }

  const input = parseResult.right;

  // Inside boundary - types are trusted
  const result = await Effect.runPromise(
    withdraw(account, input.amount)
  );

  return c.json(result);
});

// Internal code - no runtime validation needed
function calculateInterest(account: Account): number {
  // Account is already validated - trust the types
  return account.balance * 0.05;
}
```

### Effect Platform HTTP Integration

For full Effect-based HTTP services, use `@effect/platform`:

```typescript
import { HttpApi, HttpApiEndpoint, HttpApiGroup } from '@effect/platform';
import { Schema } from 'effect';

// Define API schema with Effect
const WithdrawRequest = Schema.Struct({
  accountId: Schema.String,
  amount: Schema.Number.pipe(Schema.positive())
});

const WithdrawResponse = Schema.Struct({
  newBalance: Schema.Number
});

// Define API endpoint
const withdrawEndpoint = HttpApiEndpoint.post('withdraw', '/withdraw')
  .setPayload(WithdrawRequest)
  .addSuccess(WithdrawResponse);

// Wire up to Effect handler
const withdrawHandler = HttpApiEndpoint.handle(withdrawEndpoint, ({ payload }) =>
  Effect.gen(function* () {
    const account = yield* getAccount(payload.accountId);
    const updated = yield* withdraw(account, payload.amount);
    return { newBalance: updated.balance };
  })
);
```

## Effect Schema Quick Reference

| Dafny | Effect Schema |
|-------|--------------|
| `type X = x: int \| x > 0` | `Schema.Number.pipe(Schema.int(), Schema.positive())` |
| `type X = x: int \| x >= 0` | `Schema.Number.pipe(Schema.int(), Schema.nonNegative())` |
| `type X = x: int \| a <= x <= b` | `Schema.Number.pipe(Schema.int(), Schema.between(a, b))` |
| `type X = s: string \| \|s\| > 0` | `Schema.String.pipe(Schema.minLength(1))` |
| `type X = s: string \| \|s\| <= n` | `Schema.String.pipe(Schema.maxLength(n))` |
| `datatype X = A \| B \| C` | `Schema.Literal('A', 'B', 'C')` |
| `class C { var x: int }` | `Schema.Struct({ x: Schema.Number.pipe(Schema.int()) })` |

## External References

- **Effect Documentation**: https://effect.website/docs
- **Effect Schema**: https://effect.website/docs/schema/introduction
- **Effect Schema Filters**: https://effect.website/docs/schema/filters
- **Effect Schema Branded Types**: https://effect.website/docs/schema/advanced-usage#branded-types
- **Effect Platform HTTP**: https://effect.website/docs/platform/http-server

## Examples

See `examples/` for complete implementations:
- `validated-account.ts` - Full account with all patterns
- `order-state-machine.ts` - TLA+-derived state machine
- `api-validation.ts` - HTTP API with Effect Schema validation
