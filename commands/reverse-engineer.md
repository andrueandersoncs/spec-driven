---
description: Extract specifications from existing codebase
argument-hint: [path]
allowed-tools: Read, Write, Glob, Grep, AskUserQuestion
model: sonnet
---

# Reverse Engineering

Extract formal specifications from existing code to recover user intent.

## Target Selection

If $ARGUMENTS provided, focus on that path (file or directory).
If no argument, analyze entire project from current directory.

## Phase 1: Codebase Analysis

### Identify Structure

Scan codebase for:
- Type definitions (interfaces, types, classes)
- Validation logic (Zod schemas, joi, io-ts, manual checks)
- Business entities (models, domains)
- API contracts (OpenAPI, route definitions)

```
Glob: **/*.ts, **/*.tsx
Grep: interface|type|class|z\.|schema
```

### Identify Behavior

Scan for:
- State machines (switch on state, status enums)
- Event handlers (on*, handle*, process*)
- Async workflows (sagas, effects, queues)
- Transaction boundaries (BEGIN, COMMIT, ROLLBACK)

```
Grep: state|status|enum|handler|process|transaction
```

### Identify Constraints

Look for:
- Validation checks (if statements, guards)
- Assertions (assert, invariant, require)
- Error conditions (throw, return error)
- Business rules (comments mentioning "must", "never", "always")

## Phase 2: Structure Extraction

### Extract Types

For each significant type found:

```typescript
// Found in code:
interface Account {
  id: string;
  balance: number;
  status: 'active' | 'suspended' | 'closed';
}
```

Generate Dafny:
```dafny
datatype AccountStatus = Active | Suspended | Closed

class Account {
  var id: string
  var balance: int
  var status: AccountStatus
}
```

### Extract Validation

For each validation found:

```typescript
// Found in code:
const schema = z.object({
  amount: z.number().positive(),
  accountId: z.string().uuid()
});
```

Generate assertion:
```json
{
  "id": "A-RE-001",
  "natural": "Amount must be positive",
  "type": "data_constraint",
  "category": "structure",
  "status": "inferred",
  "source": "src/validation/withdraw.ts:15"
}
```

### Extract Invariants

For each class/entity with state constraints:

```typescript
// Found in code:
if (this.balance < 0) {
  throw new Error('Balance cannot be negative');
}
```

Generate Dafny invariant:
```dafny
invariant balance >= 0
```

### Extract Contracts

For each function with validation:

```typescript
// Found in code:
function withdraw(account: Account, amount: number) {
  if (amount <= 0) throw new Error('Invalid amount');
  if (amount > account.balance) throw new Error('Insufficient funds');
  // ...
}
```

Generate Dafny method:
```dafny
method Withdraw(amount: int) returns (success: bool)
  requires amount > 0
  requires amount <= balance
```

## Phase 3: Behavior Extraction

### Extract State Machines

For each state/status pattern:

```typescript
// Found in code:
type OrderStatus = 'pending' | 'confirmed' | 'shipped' | 'delivered';

function confirmOrder(order) {
  if (order.status !== 'pending') throw new Error();
  order.status = 'confirmed';
}
```

Generate TLA+:
```tla
VARIABLES orderStatus

Init == orderStatus = "pending"

Confirm ==
  /\ orderStatus = "pending"
  /\ orderStatus' = "confirmed"
```

### Extract Safety Properties

From error conditions and guards:

```typescript
// Found in code:
if (alreadyProcessed[orderId]) {
  throw new Error('Order already processed');
}
```

Generate TLA+ safety:
```tla
\* Never process same order twice
NoDoubleProcessing ==
  [][~(ProcessOrder /\ orderId \in processed)]_vars
```

### Extract Liveness Properties

From async operations and eventual actions:

```typescript
// Found in code:
// Retry until successful
while (!success && retries < maxRetries) {
  success = await attempt();
  retries++;
}
```

Generate TLA+ liveness:
```tla
\* Request eventually succeeds or exhausts retries
RequestCompletion ==
  Request ~> (Success \/ RetriesExhausted)
```

## Phase 4: User Confirmation

Present extracted assertions for confirmation.

**Question**: "I extracted these assertions from your code. Please confirm which are accurate."

For each assertion, show:
- Natural language statement
- Source location in code
- Proposed classification

**Options**: Each assertion as selectable option

### Handle Inaccurate Extractions

If user marks extraction as wrong:
- Ask what the actual intent was
- Update assertion with corrected version
- Mark source as needing review

### Handle Missing Assertions

After extraction:
- Ask if there are requirements not visible in code
- Add manually stated requirements
- Note gap between code and intent

## Phase 5: Spec Generation

Generate formal specifications:

1. Create `specs/assertions.json` with all confirmed assertions
2. Generate `specs/dafny/structure.dfy` from structure assertions
3. Generate `specs/tla/behavior.tla` from behavior assertions
4. Add source traceability linking spec to original code

## Phase 6: Gap Analysis

Compare extracted spec to original code:

### Coverage Report

```
Extraction Summary
==================
Types analyzed: 15
Validations found: 23
State machines found: 3
Assertions extracted: 41

Coverage:
- Entities with invariants: 8/15 (53%)
- Functions with contracts: 12/30 (40%)
- State transitions documented: 18/25 (72%)

Gaps identified:
- No validation found for: UserInput, ConfigOptions
- No state machine for: NotificationService
- Missing error handling in: PaymentProcessor
```

### Recommendations

Suggest areas needing attention:
- Functions without clear contracts
- State machines without full transition coverage
- Missing validation at boundaries
- Implicit assumptions not captured

## Output

Create specification files and summary:

```
specs/
├── dafny/
│   └── structure.dfy    # Extracted structure spec
├── tla/
│   ├── behavior.tla     # Extracted behavior spec
│   └── behavior.cfg     # TLC configuration
└── assertions.json      # All assertions with traceability
```

Report:
- Total assertions extracted
- Breakdown by category (structure/behavior)
- User confirmations received
- Gaps and recommendations
- Next step: Run `/verify` to check extracted specs
