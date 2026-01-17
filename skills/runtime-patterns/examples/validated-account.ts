/**
 * @generated example
 * Complete example of runtime validation patterns for an Account entity
 * Demonstrates: Zod schemas, branded types, Effect errors, contract checking
 */

import { z } from 'zod';

// =============================================================================
// BRANDED TYPES (compile-time safety)
// =============================================================================

type Brand<T, B> = T & { readonly __brand: B };

export type AccountId = Brand<string, 'AccountId'>;
export type PositiveAmount = Brand<number, 'PositiveAmount'>;
export type NonNegativeBalance = Brand<number, 'NonNegativeBalance'>;

// Smart constructors
export function accountId(s: string): AccountId | null {
  return s.length > 0 ? (s as AccountId) : null;
}

export function positiveAmount(n: number): PositiveAmount | null {
  return n > 0 && Number.isFinite(n) ? (n as PositiveAmount) : null;
}

export function nonNegativeBalance(n: number): NonNegativeBalance | null {
  return n >= 0 && Number.isFinite(n) ? (n as NonNegativeBalance) : null;
}

// =============================================================================
// ZOD SCHEMAS (runtime validation at boundaries)
// =============================================================================

/**
 * @source-assertion A-001: "Account balance never negative"
 * @source-spec specs/dafny/structure.dfy:5-8
 */
export const AccountSchema = z.object({
  id: z.string().min(1).transform((s): AccountId => s as AccountId),
  balance: z.number().nonnegative().transform((n): NonNegativeBalance => n as NonNegativeBalance),
  name: z.string().min(1).max(100),
  createdAt: z.date()
});

export type Account = z.infer<typeof AccountSchema>;

/**
 * @source-assertion A-002: "Withdraw amount must be positive"
 * @source-spec specs/dafny/structure.dfy:15-17
 */
export const WithdrawInputSchema = z.object({
  accountId: z.string().min(1),
  amount: z.number().positive()
});

export type WithdrawInput = z.infer<typeof WithdrawInputSchema>;

// =============================================================================
// DISCRIMINATED UNION ERRORS (structured error handling)
// =============================================================================

export type WithdrawError =
  | { readonly _tag: 'AccountNotFound'; readonly accountId: string }
  | { readonly _tag: 'InvalidAmount'; readonly amount: number; readonly reason: string }
  | { readonly _tag: 'InsufficientFunds'; readonly balance: number; readonly requested: number };

export type WithdrawResult<T> =
  | { readonly success: true; readonly value: T }
  | { readonly success: false; readonly error: WithdrawError };

// Error constructors
export const WithdrawError = {
  accountNotFound: (accountId: string): WithdrawError => ({
    _tag: 'AccountNotFound',
    accountId
  }),
  invalidAmount: (amount: number, reason: string): WithdrawError => ({
    _tag: 'InvalidAmount',
    amount,
    reason
  }),
  insufficientFunds: (balance: number, requested: number): WithdrawError => ({
    _tag: 'InsufficientFunds',
    balance,
    requested
  })
};

// =============================================================================
// DOMAIN LOGIC (pure functions with typed errors)
// =============================================================================

/**
 * @source-assertion A-002: "Withdraw requires positive amount"
 * @source-assertion A-003: "Withdraw requires sufficient funds"
 * @source-assertion A-001: "Balance never negative after withdraw"
 * @source-spec specs/dafny/structure.dfy:15-25
 */
export function withdraw(
  account: Account,
  amount: number
): WithdrawResult<Account> {
  // Precondition: amount > 0
  if (amount <= 0) {
    return {
      success: false,
      error: WithdrawError.invalidAmount(amount, 'Amount must be positive')
    };
  }

  // Precondition: amount <= balance
  if (amount > account.balance) {
    return {
      success: false,
      error: WithdrawError.insufficientFunds(account.balance, amount)
    };
  }

  // Postcondition: new balance = old balance - amount
  // Invariant: balance >= 0 (guaranteed by preconditions)
  const newBalance = nonNegativeBalance(account.balance - amount);

  if (newBalance === null) {
    // This should never happen if preconditions are correct
    throw new Error('Invariant violation: balance became negative');
  }

  return {
    success: true,
    value: {
      ...account,
      balance: newBalance
    }
  };
}

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
  fn: (...args: Args) => Result,
  contract: Contract<Args, Result>
): (...args: Args) => Result {
  return (...args: Args): Result => {
    // Check precondition
    if (contract.pre && !contract.pre(...args)) {
      throw new ContractViolation(contract.assertionId, 'precondition', { args });
    }

    const result = fn(...args);

    // Check postcondition
    if (contract.post && !contract.post(result, ...args)) {
      throw new ContractViolation(contract.assertionId, 'postcondition', { args, result });
    }

    return result;
  };
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
    if (!result.success) return true; // Errors are valid outcomes
    return (
      result.value.balance === account.balance - amount &&
      result.value.balance >= 0
    );
  }
});

// =============================================================================
// EXHAUSTIVE ERROR HANDLING
// =============================================================================

export function handleWithdrawError(error: WithdrawError): string {
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
}

// =============================================================================
// USAGE EXAMPLE
// =============================================================================

export function example() {
  // Create account (validated at boundary)
  const accountData = AccountSchema.parse({
    id: 'acc-123',
    balance: 100,
    name: 'Test Account',
    createdAt: new Date()
  });

  // Withdraw (type-safe, error-tracked)
  const result = withdraw(accountData, 50);

  if (result.success) {
    console.log(`New balance: ${result.value.balance}`);
  } else {
    console.error(handleWithdrawError(result.error));
  }

  // With contract checking (development)
  try {
    const checkedResult = withdrawChecked(accountData, 200);
  } catch (e) {
    if (e instanceof ContractViolation) {
      console.error(`Contract [${e.assertionId}] ${e.type} failed`);
    }
  }
}
