/**
 * @generated example
 * Complete example of runtime validation patterns for an Account entity
 * Demonstrates: Effect Schema, branded types, Effect errors, contract checking
 */

import { Schema, Effect, Data, Either, Brand } from 'effect';

// =============================================================================
// BRANDED TYPES (compile-time safety with Effect Schema)
// =============================================================================

const AccountId = Schema.String.pipe(
  Schema.minLength(1),
  Schema.brand('AccountId')
);
export type AccountId = typeof AccountId.Type;

const PositiveAmount = Schema.Number.pipe(
  Schema.positive(),
  Schema.finite(),
  Schema.brand('PositiveAmount')
);
export type PositiveAmount = typeof PositiveAmount.Type;

const NonNegativeBalance = Schema.Number.pipe(
  Schema.nonNegative(),
  Schema.finite(),
  Schema.brand('NonNegativeBalance')
);
export type NonNegativeBalance = typeof NonNegativeBalance.Type;

// Smart constructors using Effect Schema
export const accountId = (s: string): AccountId | null => {
  const result = Schema.decodeUnknownEither(AccountId)(s);
  return Either.isRight(result) ? result.right : null;
};

export const positiveAmount = (n: number): PositiveAmount | null => {
  const result = Schema.decodeUnknownEither(PositiveAmount)(n);
  return Either.isRight(result) ? result.right : null;
};

export const nonNegativeBalance = (n: number): NonNegativeBalance | null => {
  const result = Schema.decodeUnknownEither(NonNegativeBalance)(n);
  return Either.isRight(result) ? result.right : null;
};

// =============================================================================
// EFFECT SCHEMAS (runtime validation at boundaries)
// =============================================================================

/**
 * @source-assertion A-001: "Account balance never negative"
 * @source-spec specs/dafny/structure.dfy:5-8
 */
export const AccountSchema = Schema.Struct({
  id: AccountId,
  balance: NonNegativeBalance,
  name: Schema.String.pipe(Schema.minLength(1), Schema.maxLength(100)),
  createdAt: Schema.Date
});

export type Account = typeof AccountSchema.Type;

/**
 * @source-assertion A-002: "Withdraw amount must be positive"
 * @source-spec specs/dafny/structure.dfy:15-17
 */
export const WithdrawInputSchema = Schema.Struct({
  accountId: Schema.String.pipe(Schema.minLength(1)),
  amount: Schema.Number.pipe(Schema.positive())
});

export type WithdrawInput = typeof WithdrawInputSchema.Type;

// =============================================================================
// TAGGED ERROR TYPES (structured error handling with Effect)
// =============================================================================

export class AccountNotFound extends Data.TaggedError('AccountNotFound')<{
  readonly accountId: string;
}> {}

export class InvalidAmount extends Data.TaggedError('InvalidAmount')<{
  readonly amount: number;
  readonly reason: string;
}> {}

export class InsufficientFunds extends Data.TaggedError('InsufficientFunds')<{
  readonly balance: number;
  readonly requested: number;
}> {}

export type WithdrawError = AccountNotFound | InvalidAmount | InsufficientFunds;

// =============================================================================
// DOMAIN LOGIC (Effect-based with typed errors)
// =============================================================================

/**
 * @source-assertion A-002: "Withdraw requires positive amount"
 * @source-assertion A-003: "Withdraw requires sufficient funds"
 * @source-assertion A-001: "Balance never negative after withdraw"
 * @source-spec specs/dafny/structure.dfy:15-25
 */
export const withdraw = (
  account: Account,
  amount: number
): Effect.Effect<Account, WithdrawError> =>
  Effect.gen(function* () {
    // Precondition: amount > 0
    if (amount <= 0) {
      return yield* Effect.fail(
        new InvalidAmount({ amount, reason: 'Amount must be positive' })
      );
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

    // Postcondition: new balance = old balance - amount
    // Invariant: balance >= 0 (guaranteed by preconditions)
    const newBalance = nonNegativeBalance(account.balance - amount);

    if (newBalance === null) {
      // This should never happen if preconditions are correct
      throw new Error('Invariant violation: balance became negative');
    }

    return {
      ...account,
      balance: newBalance
    };
  });

// =============================================================================
// CONTRACT CHECKING (development mode)
// =============================================================================

export class ContractViolation extends Error {
  constructor(
    public readonly assertionId: string,
    public readonly type: 'precondition' | 'postcondition' | 'invariant',
    public readonly context: unknown
  ) {
    super(`Contract violation [${assertionId}]: ${type} failed`);
    this.name = 'ContractViolation';
  }
}

interface Contract<Args extends unknown[], Result> {
  assertionId: string;
  pre?: (...args: Args) => boolean;
  post?: (result: Result, ...args: Args) => boolean;
}

function withContract<Args extends unknown[], Result>(
  fn: (...args: Args) => Effect.Effect<Result, WithdrawError>,
  contract: Contract<Args, Result>
): (...args: Args) => Effect.Effect<Result, WithdrawError> {
  return (...args: Args) =>
    Effect.gen(function* () {
      // Check precondition
      if (contract.pre && !contract.pre(...args)) {
        throw new ContractViolation(contract.assertionId, 'precondition', { args });
      }

      const result = yield* fn(...args);

      // Check postcondition
      if (contract.post && !contract.post(result, ...args)) {
        throw new ContractViolation(contract.assertionId, 'postcondition', { args, result });
      }

      return result;
    });
}

// Withdraw with contract checking enabled
export const withdrawChecked = withContract(withdraw, {
  assertionId: 'A-001,A-002,A-003',
  pre: (account, amount) => {
    // All preconditions from Dafny spec
    return amount > 0 && amount <= account.balance;
  },
  post: (result, account, amount) => {
    // All postconditions from Dafny spec
    return (
      result.balance === account.balance - amount &&
      result.balance >= 0
    );
  }
});

// =============================================================================
// EXHAUSTIVE ERROR HANDLING
// =============================================================================

export const handleWithdrawError = (error: WithdrawError): string => {
  switch (error._tag) {
    case 'AccountNotFound':
      return `Account ${error.accountId} not found`;
    case 'InvalidAmount':
      return `Invalid amount ${error.amount}: ${error.reason}`;
    case 'InsufficientFunds':
      return `Insufficient funds: balance is ${error.balance}, requested ${error.requested}`;
    default:
      // TypeScript ensures exhaustiveness
      const _exhaustive: never = error;
      return _exhaustive;
  }
};

// =============================================================================
// USAGE EXAMPLE
// =============================================================================

export const example = async () => {
  // Create account (validated at boundary)
  const accountData = Schema.decodeUnknownSync(AccountSchema)({
    id: 'acc-123',
    balance: 100,
    name: 'Test Account',
    createdAt: new Date()
  });

  // Withdraw (type-safe, error-tracked)
  const result = await Effect.runPromiseExit(withdraw(accountData, 50));

  if (result._tag === 'Success') {
    console.log(`New balance: ${result.value.balance}`);
  } else if (result._tag === 'Failure') {
    const error = result.cause;
    if (error._tag === 'Fail') {
      console.error(handleWithdrawError(error.error));
    }
  }

  // With comprehensive error handling using catchTags
  const program = Effect.gen(function* () {
    const updated = yield* withdraw(accountData, 200);
    return updated;
  }).pipe(
    Effect.catchTags({
      InvalidAmount: (e) => Effect.succeed({ error: `Invalid: ${e.reason}` }),
      InsufficientFunds: (e) => Effect.succeed({ error: `Insufficient: ${e.balance} < ${e.requested}` }),
      AccountNotFound: (e) => Effect.succeed({ error: `Not found: ${e.accountId}` })
    })
  );

  const handled = await Effect.runPromise(program);
  console.log(handled);

  // With contract checking (development)
  try {
    await Effect.runPromise(withdrawChecked(accountData, 200));
  } catch (e) {
    if (e instanceof ContractViolation) {
      console.error(`Contract [${e.assertionId}] ${e.type} failed`);
    }
  }
};
