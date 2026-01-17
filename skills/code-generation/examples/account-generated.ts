/**
 * Example: Generated TypeScript from Dafny/TLA+ Specifications
 * Demonstrates spec-driven code generation patterns using Effect
 *
 * @generated
 * @source-spec specs/dafny/account.dfy
 * @source-spec specs/tla/account.tla
 */

import { Schema, Effect, Data, Either } from 'effect';

//===========================================================================
// TYPES & SCHEMAS (from Dafny refinement types)
//===========================================================================

/**
 * @generated
 * @source-assertion A-001: "Balance can be negative up to overdraft limit"
 * @source-spec specs/dafny/account.dfy:5-6
 */
export const BalanceSchema = Schema.Number.pipe(
  Schema.int(),
  Schema.greaterThanOrEqualTo(-100)
);
export type Balance = typeof BalanceSchema.Type;

/**
 * @generated
 * @source-assertion A-002: "Transaction amounts must be positive"
 * @source-spec specs/dafny/account.dfy:8-9
 */
export const PositiveAmountSchema = Schema.Number.pipe(
  Schema.int(),
  Schema.positive()
);
export type PositiveAmount = typeof PositiveAmountSchema.Type;

/**
 * @generated
 * @source-assertion A-003: "Account has balance, owner, and state"
 * @source-spec specs/dafny/account.dfy:12-15
 */
export const AccountStateSchema = Schema.Literal('active', 'frozen', 'closed');
export type AccountState = typeof AccountStateSchema.Type;

export const AccountSchema = Schema.Struct({
  id: Schema.String.pipe(Schema.uuid()),
  balance: BalanceSchema,
  owner: Schema.String.pipe(Schema.minLength(1), Schema.maxLength(100)),
  state: AccountStateSchema
});
export type Account = typeof AccountSchema.Type;

/**
 * @generated
 * @source-spec specs/tla/account.tla:15-17
 */
export const TransactionTypeSchema = Schema.Literal('deposit', 'withdraw');

export const TransactionSchema = Schema.Struct({
  type: TransactionTypeSchema,
  amount: Schema.Number.pipe(Schema.int(), Schema.positive()),
  success: Schema.Boolean,
  timestamp: Schema.Date
});
export type Transaction = typeof TransactionSchema.Type;

//===========================================================================
// ERROR TYPES (from Dafny preconditions)
//===========================================================================

export class InvalidAmount extends Data.TaggedError('InvalidAmount')<{
  readonly amount: number;
}> {}

export class AccountNotActive extends Data.TaggedError('AccountNotActive')<{
  readonly state: AccountState;
}> {}

export class WouldExceedLimit extends Data.TaggedError('WouldExceedLimit')<{
  readonly currentBalance: number;
  readonly amount: number;
}> {}

export class InsufficientFunds extends Data.TaggedError('InsufficientFunds')<{
  readonly balance: number;
  readonly requested: number;
}> {}

//===========================================================================
// VALIDATION (from Dafny preconditions)
//===========================================================================

/**
 * @generated
 * @source-assertion A-010: "Deposit requires positive amount"
 * @source-spec specs/dafny/account.dfy:28
 */
export type DepositError = InvalidAmount | AccountNotActive | WouldExceedLimit;

export const validateDeposit = (
  account: Account,
  amount: number
): Effect.Effect<void, DepositError> =>
  Effect.gen(function* () {
    if (amount <= 0) {
      return yield* Effect.fail(new InvalidAmount({ amount }));
    }
    if (account.state !== 'active') {
      return yield* Effect.fail(new AccountNotActive({ state: account.state }));
    }
    // Assume max balance of 1_000_000 for practical purposes
    if (account.balance + amount > 1_000_000) {
      return yield* Effect.fail(
        new WouldExceedLimit({ currentBalance: account.balance, amount })
      );
    }
  });

/**
 * @generated
 * @source-assertion A-011: "Withdraw requires positive amount and sufficient funds"
 * @source-spec specs/dafny/account.dfy:35-36
 */
export type WithdrawError = InvalidAmount | AccountNotActive | InsufficientFunds;

export const validateWithdraw = (
  account: Account,
  amount: number
): Effect.Effect<void, WithdrawError> =>
  Effect.gen(function* () {
    if (amount <= 0) {
      return yield* Effect.fail(new InvalidAmount({ amount }));
    }
    if (account.state !== 'active') {
      return yield* Effect.fail(new AccountNotActive({ state: account.state }));
    }
    // Allow overdraft up to -100
    if (account.balance - amount < -100) {
      return yield* Effect.fail(
        new InsufficientFunds({ balance: account.balance, requested: amount })
      );
    }
  });

//===========================================================================
// DOMAIN LOGIC (from Dafny method bodies)
//===========================================================================

/**
 * @generated
 * @source-assertion A-012: "Deposit increases balance by exact amount"
 * @source-spec specs/dafny/account.dfy:29-30
 */
export type DepositResult = { account: Account; transaction: Transaction };

export const deposit = (
  account: Account,
  amount: number
): Effect.Effect<DepositResult, DepositError> =>
  Effect.gen(function* () {
    yield* validateDeposit(account, amount);

    // Postcondition: balance == old(balance) + amount
    const updatedAccount: Account = {
      ...account,
      balance: account.balance + amount
    };

    const transaction: Transaction = {
      type: 'deposit',
      amount,
      success: true,
      timestamp: new Date()
    };

    return { account: updatedAccount, transaction };
  });

/**
 * @generated
 * @source-assertion A-013: "Successful withdrawal decreases balance by exact amount"
 * @source-assertion A-014: "Failed withdrawal leaves balance unchanged"
 * @source-spec specs/dafny/account.dfy:37-42
 */
export type WithdrawResult = { account: Account; transaction: Transaction };

export const withdraw = (
  account: Account,
  amount: number
): Effect.Effect<WithdrawResult, WithdrawError> =>
  Effect.gen(function* () {
    yield* validateWithdraw(account, amount);

    // Postcondition: balance == old(balance) - amount
    const updatedAccount: Account = {
      ...account,
      balance: account.balance - amount
    };

    const transaction: Transaction = {
      type: 'withdraw',
      amount,
      success: true,
      timestamp: new Date()
    };

    return { account: updatedAccount, transaction };
  });

//===========================================================================
// STATE MACHINE (from TLA+ actions)
//===========================================================================

/**
 * @generated
 * @source-spec specs/tla/account.tla:45-65
 */
export const accountTransitions: Record<AccountState, AccountState[]> = {
  active: ['frozen', 'closed'],
  frozen: ['active', 'closed'],
  closed: [] // Terminal state
};

export const canTransition = (from: AccountState, to: AccountState): boolean =>
  accountTransitions[from].includes(to);

/**
 * @generated
 * @source-assertion A-020: "Can only close account with zero balance"
 * @source-spec specs/tla/account.tla:62-65
 */
export class InvalidTransition extends Data.TaggedError('InvalidTransition')<{
  readonly from: AccountState;
  readonly to: AccountState;
}> {}

export class CannotCloseWithBalance extends Data.TaggedError('CannotCloseWithBalance')<{
  readonly balance: number;
}> {}

export type StateTransitionError = InvalidTransition | CannotCloseWithBalance;

export const transitionState = (
  account: Account,
  to: AccountState
): Effect.Effect<Account, StateTransitionError> =>
  Effect.gen(function* () {
    if (!canTransition(account.state, to)) {
      return yield* Effect.fail(
        new InvalidTransition({ from: account.state, to })
      );
    }

    // Special check: can only close if balance is zero
    if (to === 'closed' && account.balance !== 0) {
      return yield* Effect.fail(
        new CannotCloseWithBalance({ balance: account.balance })
      );
    }

    return { ...account, state: to };
  });

//===========================================================================
// PROPERTY-BASED TEST HELPERS
//===========================================================================

/**
 * Invariant check: balance within limits
 * @source-assertion A-001
 */
export const checkBalanceInvariant = (account: Account): boolean =>
  account.balance >= -100;

/**
 * Invariant check: closed account has zero balance
 * @source-assertion A-020
 */
export const checkClosedInvariant = (account: Account): boolean =>
  account.state !== 'closed' || account.balance === 0;
