/**
 * Example: Generated TypeScript from Dafny/TLA+ Specifications
 * Demonstrates spec-driven code generation patterns
 *
 * @generated
 * @source-spec specs/dafny/account.dfy
 * @source-spec specs/tla/account.tla
 */

import { z } from 'zod';

//===========================================================================
// TYPES & SCHEMAS (from Dafny refinement types)
//===========================================================================

/**
 * @generated
 * @source-assertion A-001: "Balance can be negative up to overdraft limit"
 * @source-spec specs/dafny/account.dfy:5-6
 */
export const BalanceSchema = z.number().int().min(-100);
export type Balance = z.infer<typeof BalanceSchema>;

/**
 * @generated
 * @source-assertion A-002: "Transaction amounts must be positive"
 * @source-spec specs/dafny/account.dfy:8-9
 */
export const PositiveAmountSchema = z.number().int().positive();
export type PositiveAmount = z.infer<typeof PositiveAmountSchema>;

/**
 * @generated
 * @source-assertion A-003: "Account has balance, owner, and state"
 * @source-spec specs/dafny/account.dfy:12-15
 */
export const AccountSchema = z.object({
  id: z.string().uuid(),
  balance: BalanceSchema,
  owner: z.string().min(1).max(100),
  state: z.enum(['active', 'frozen', 'closed'])
});
export type Account = z.infer<typeof AccountSchema>;

/**
 * @generated
 * @source-spec specs/tla/account.tla:15-17
 */
export const TransactionSchema = z.object({
  type: z.enum(['deposit', 'withdraw']),
  amount: z.number().int().positive(),
  success: z.boolean(),
  timestamp: z.date()
});
export type Transaction = z.infer<typeof TransactionSchema>;

//===========================================================================
// VALIDATION (from Dafny preconditions)
//===========================================================================

/**
 * @generated
 * @source-assertion A-010: "Deposit requires positive amount"
 * @source-spec specs/dafny/account.dfy:28
 */
export type DepositValidation =
  | { valid: true }
  | { valid: false; error: 'INVALID_AMOUNT' | 'ACCOUNT_NOT_ACTIVE' | 'WOULD_EXCEED_LIMIT' };

export function validateDeposit(
  account: Account,
  amount: number
): DepositValidation {
  if (amount <= 0) {
    return { valid: false, error: 'INVALID_AMOUNT' };
  }
  if (account.state !== 'active') {
    return { valid: false, error: 'ACCOUNT_NOT_ACTIVE' };
  }
  // Assume max balance of 1_000_000 for practical purposes
  if (account.balance + amount > 1_000_000) {
    return { valid: false, error: 'WOULD_EXCEED_LIMIT' };
  }
  return { valid: true };
}

/**
 * @generated
 * @source-assertion A-011: "Withdraw requires positive amount and sufficient funds"
 * @source-spec specs/dafny/account.dfy:35-36
 */
export type WithdrawValidation =
  | { valid: true }
  | { valid: false; error: 'INVALID_AMOUNT' | 'ACCOUNT_NOT_ACTIVE' | 'INSUFFICIENT_FUNDS' };

export function validateWithdraw(
  account: Account,
  amount: number
): WithdrawValidation {
  if (amount <= 0) {
    return { valid: false, error: 'INVALID_AMOUNT' };
  }
  if (account.state !== 'active') {
    return { valid: false, error: 'ACCOUNT_NOT_ACTIVE' };
  }
  // Allow overdraft up to -100
  if (account.balance - amount < -100) {
    return { valid: false, error: 'INSUFFICIENT_FUNDS' };
  }
  return { valid: true };
}

//===========================================================================
// DOMAIN LOGIC (from Dafny method bodies)
//===========================================================================

/**
 * @generated
 * @source-assertion A-012: "Deposit increases balance by exact amount"
 * @source-spec specs/dafny/account.dfy:29-30
 */
export type DepositResult =
  | { success: true; account: Account; transaction: Transaction }
  | { success: false; error: string };

export function deposit(
  account: Account,
  amount: number
): DepositResult {
  const validation = validateDeposit(account, amount);
  if (!validation.valid) {
    return { success: false, error: validation.error };
  }

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

  return { success: true, account: updatedAccount, transaction };
}

/**
 * @generated
 * @source-assertion A-013: "Successful withdrawal decreases balance by exact amount"
 * @source-assertion A-014: "Failed withdrawal leaves balance unchanged"
 * @source-spec specs/dafny/account.dfy:37-42
 */
export type WithdrawResult =
  | { success: true; account: Account; transaction: Transaction }
  | { success: false; error: string; transaction?: Transaction };

export function withdraw(
  account: Account,
  amount: number
): WithdrawResult {
  const validation = validateWithdraw(account, amount);
  if (!validation.valid) {
    // Log failed attempt
    const failedTransaction: Transaction = {
      type: 'withdraw',
      amount,
      success: false,
      timestamp: new Date()
    };
    return {
      success: false,
      error: validation.error,
      transaction: failedTransaction
    };
  }

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

  return { success: true, account: updatedAccount, transaction };
}

//===========================================================================
// STATE MACHINE (from TLA+ actions)
//===========================================================================

/**
 * @generated
 * @source-spec specs/tla/account.tla:45-65
 */
export type AccountState = 'active' | 'frozen' | 'closed';

export const accountTransitions: Record<AccountState, AccountState[]> = {
  active: ['frozen', 'closed'],
  frozen: ['active', 'closed'],
  closed: [] // Terminal state
};

export function canTransition(from: AccountState, to: AccountState): boolean {
  return accountTransitions[from].includes(to);
}

/**
 * @generated
 * @source-assertion A-020: "Can only close account with zero balance"
 * @source-spec specs/tla/account.tla:62-65
 */
export type StateTransitionResult =
  | { success: true; account: Account }
  | { success: false; error: string };

export function transitionState(
  account: Account,
  to: AccountState
): StateTransitionResult {
  if (!canTransition(account.state, to)) {
    return {
      success: false,
      error: `Cannot transition from ${account.state} to ${to}`
    };
  }

  // Special check: can only close if balance is zero
  if (to === 'closed' && account.balance !== 0) {
    return {
      success: false,
      error: 'Cannot close account with non-zero balance'
    };
  }

  return {
    success: true,
    account: { ...account, state: to }
  };
}

//===========================================================================
// PROPERTY-BASED TEST HELPERS
//===========================================================================

/**
 * Invariant check: balance within limits
 * @source-assertion A-001
 */
export function checkBalanceInvariant(account: Account): boolean {
  return account.balance >= -100;
}

/**
 * Invariant check: closed account has zero balance
 * @source-assertion A-020
 */
export function checkClosedInvariant(account: Account): boolean {
  return account.state !== 'closed' || account.balance === 0;
}
