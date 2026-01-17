# Goal: Executable Ontology for Software Specification

## The Vision

Create a Claude Code plugin that enables the generation of **correct and complete software** by building an **executable ontology** that models user intent using formal logic.

This capability is **bi-directional**:
- **Forward**: Derive software from user intent
- **Reverse**: Recover user intent from existing software

## Agent Architecture

This plugin enables Claude Code to act as a **specification-driven development agent**.

**Claude Code performs:**

| Responsibility | Description |
|----------------|-------------|
| **Domain Probing** | Asks questions, interprets answers, loads archetype/domain templates |
| **Assertion Generation** | Proposes candidate assertions based on conversation context |
| **Classification** | Routes assertions to Dafny (structure) vs TLA+ (behavior) based on taxonomy |
| **Formal Model Authoring** | Writes and maintains `.dfy` and `.tla` specification files |
| **Verification Orchestration** | Invokes `dafny verify` and `tlc` via Bash, interprets output |
| **Conflict Resolution** | Explains verification failures to user, proposes fixes |
| **Code Generation** | Extracts verified code from Dafny or writes spec-guided implementations |
| **Traceability Maintenance** | Links generated artifacts back to confirmed assertions |

**The user's role:**

- Provide natural language requirements
- Provide feedback on assertions (confirm, deny, refine, or offer alternatives)
- Fill in parameters for parameterized assertions
- Resolve conflicts when Claude surfaces contradictions
- Signal completeness ("that's everything for this scope")

**External tools (invoked by Claude via Bash):**

| Tool | Purpose |
|------|---------|
| `dafny verify` | Check structural correctness (Z3-backed) |
| `dafny build` | Extract verified code to target language |
| `tlc` | Model-check behavioral properties |
| Target compilers/runtimes | Build and test generated code |

**Key principle**: Claude is the active agent orchestrating the entire pipeline. The formal tools provide verification oracles, but Claude drives the process, maintains state across context windows, and mediates between user intent and formal specifications.

## Core Principle

Software specification requires two co-evolving formal models:

| Model | Purpose | Formalism | Verifier |
|-------|---------|-----------|----------|
| **Structure Model** | Entities, relationships, data constraints, contracts | Dafny | Dafny verifier (Z3-backed) |
| **Behavior Model** | State evolution, concurrency, temporal properties | TLA+ | TLC model checker |

The key distinction is **space vs. time**:
- **Dafny** (Structure): What is true at any single point in time
- **TLA+** (Behavior): What is true across sequences of states

### Model Interconnection

The models are not independent — they share a common semantic foundation:

```
Dafny class Account {           ←→    TLA+ VARIABLE account
  var balance: int                    account ∈ Int
  invariant balance >= 0              Invariant: account >= 0

  method Withdraw(amt: int)     ←→    Withdraw(amt) ==
    requires amt <= balance             /\ amt <= account
    ensures balance == old(balance) - amt   /\ account' = account - amt
}
```

**Translation rules**:
1. Dafny `class` → TLA+ `VARIABLE` (one per instance, or a function for collections)
2. Dafny `invariant` → TLA+ `Invariant` (checked at every state)
3. Dafny `method` → TLA+ action (state transition)
4. Dafny `requires`/`ensures` → TLA+ action precondition/postcondition

**Consistency checking**: When both models exist, we verify:
- Every TLA+ action preserves Dafny invariants
- Every Dafny method signature has a corresponding TLA+ action
- Reachable states in TLA+ satisfy Dafny refinement types

## Assertion Taxonomy

User intent decomposes into assertions. Each assertion maps to a specific formal construct:

### Structure Assertions → Dafny

| Category | Example (Natural Language) | Dafny Construct |
|----------|---------------------------|-----------------|
| **Data constraint** | "User age must be positive" | `type Age = x: int \| x > 0` |
| **Entity invariant** | "Account balance never negative" | `invariant balance >= 0` |
| **Precondition** | "Can only withdraw if sufficient funds" | `requires amount <= balance` |
| **Postcondition** | "Deposit increases balance by exact amount" | `ensures balance == old(balance) + amount` |
| **Relationship** | "Every order belongs to exactly one customer" | `var customer: Customer` (non-null reference) |
| **Uniqueness** | "Email addresses are unique across users" | `predicate UniqueEmails(users: set<User>)` |

### Behavior Assertions → TLA+

| Category | Example (Natural Language) | TLA+ Construct |
|----------|---------------------------|----------------|
| **Liveness** | "Every request eventually gets a response" | `Request ~> Response` |
| **Safety** | "Never process payment twice for same order" | `[][~(ProcessPayment /\ processed)]_vars` |
| **Ordering** | "Auth must happen before any API call" | `Auth ∈ prefix(APICall)` |
| **Fairness** | "No request starves indefinitely" | `WF_vars(ProcessRequest)` |
| **State reachability** | "System can always return to idle state" | `Spec => <>[]Idle` |
| **Concurrency** | "At most one writer at a time" | `Cardinality(writers) <= 1` |

### Classification Heuristic

When the Interview Engine generates an assertion, it classifies by asking:

```
Is this about a SINGLE moment in time, or SEQUENCES of states?
├── Single moment → Dafny (Structure)
│   ├── About data shape/type? → refinement type
│   ├── About entity state? → class invariant
│   ├── About operation input? → requires
│   └── About operation output? → ensures
│
└── Sequences of states → TLA+ (Behavior)
    ├── "Eventually X happens" → liveness
    ├── "X never happens" → safety
    ├── "X before Y" → ordering
    └── "X and Y don't overlap" → mutual exclusion
```

## The Translation Pipeline

```
┌─────────────────────────────────────────────────────────────────┐
│                         USER INTENT                             │
│            (vague requirements, conversations)                  │
└───────────────────────────┬─────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│                      INTERVIEW ENGINE                           │
│                                                                 │
│  • Generate candidate assertions from user input                │
│  • User provides feedback: confirm, refine, or suggest alternatives│
│  • "It depends" triggers decomposition                          │
│  • Parameterized assertions collapse infinite search spaces     │
│                                                                 │
└───────────────────────────┬─────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│                      FORMAL MODELS                              │
│                                                                 │
│       ┌─────────────────┐       ┌─────────────────┐             │
│       │    Structure    │◄─────►│    Behavior     │             │
│       │    (Dafny)      │       │    (TLA+)       │             │
│       └────────┬────────┘       └────────┬────────┘             │
│                │                         │                       │
│                └───────────┬─────────────┘                       │
│                            │                                     │
│                ┌───────────▼───────────┐                         │
│                │  Consistency Check    │                         │
│                │  • Contradiction?     │                         │
│                │  • Implied assertions?│                         │
│                │  • Model agreement?   │                         │
│                └───────────────────────┘                         │
│                                                                  │
└───────────────────────────┬──────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│                    DERIVED ARTIFACTS                            │
│                                                                 │
│  Data Layer (persistence strategy depends on requirements)      │
│  • Types and schemas (always)                                   │
│  • DB schemas / file formats / protocol buffers / in-memory     │
│  • API contracts / CLI arg schemas / library interfaces         │
│                                                                 │
│  Validation Layer                                               │
│  • Runtime schemas (Zod, io-ts, etc.)                          │
│  • Constraints (DB, format, protocol)                          │
│  • Guards and assertions                                        │
│                                                                 │
│  Logic Layer                                                    │
│  • State machines and workflows                                 │
│  • Request/command handlers                                     │
│  • Core algorithms and transforms                               │
│                                                                 │
│  Environment Layer (derived from requirements)                  │
│  • flake.nix / Docker / none                                   │
│  • Persistence config (if stateful)                            │
│  • Auth config (if multi-user or protected)                    │
│  • Deployment manifests (if deployed vs distributed)           │
│                                                                 │
│  Verification Layer                                             │
│  • Property-based tests (from Dafny contracts)                  │
│  • Integration tests (from TLA+ traces)                        │
│  • E2E / acceptance tests (from use cases)                     │
│                                                                 │
└───────────────────────────┬─────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│                    RUNNING SOFTWARE                             │
│                                                                 │
│  Verified against formal models at every layer                  │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Interview Engine

The Interview Engine extracts formal assertions from natural language through iterative conversation. It applies the [Ralph Wiggum methodology](https://github.com/ghuntley/how-to-ralph-wiggum) pattern of tight task scoping and persistent state, but replaces markdown specs with formal verification.

### Design Principles

| Principle | Implementation |
|-----------|----------------|
| Persistent state | Dafny/TLA+ specs survive across context windows |
| Backpressure | Formal verification constrains LLM non-determinism |
| Recognition over recall | LLM generates assertions; human reviews and refines |
| Fresh context | Each assertion batch starts clean + current specs |
| Tight scoping | One assertion batch per loop iteration |

### Domain Probing (Bootstrapping)

Before the Interview Loop can generate meaningful assertions, the system must establish context. The **Domain Probing** phase solves the cold-start problem by systematically exploring the problem space.

#### The Cold-Start Problem

The Interview Loop assumes users can provide meaningful natural language input, but:
- Users often don't know what they don't know
- Initial descriptions are typically incomplete or ambiguous
- Critical requirements hide in unstated assumptions
- Domain-specific concerns may not surface without prompting

#### Probing Strategy

```
┌──────────────────────────────────────────────────────────────────┐
│                       DOMAIN PROBING PHASE                       │
│                                                                  │
│  1. Software Archetype Identification                            │
│     "What are you building?"                                     │
│     → CLI tool / Library / Web service / Desktop app / etc.      │
│     (Loads archetype-specific assertion templates)               │
│                                                                  │
│  2. Domain Classification                                        │
│     "What domain does this operate in?"                          │
│     → Finance / Healthcare / E-commerce / DevTools / etc.        │
│     (Loads domain-specific invariants and compliance reqs)       │
│                                                                  │
│  3. Actor Enumeration                                            │
│     "Who/what interacts with this system?"                       │
│     → Users, Admins, External APIs, Background jobs, etc.        │
│     (Each actor becomes a source of use cases)                   │
│                                                                  │
│  4. Capability Mapping                                           │
│     For each actor: "What can they do?"                          │
│     → CRUD operations, workflows, queries, etc.                  │
│     (Each capability becomes an assertion cluster)               │
│                                                                  │
│  5. Negative Space Exploration                                   │
│     "What is this system explicitly NOT?"                        │
│     → "Not multi-tenant" / "Not real-time" / "Not distributed"   │
│     (Prevents over-engineering, constrains solution space)       │
│                                                                  │
│  6. Boundary Identification                                      │
│     "Where does your system end?"                                │
│     → External dependencies, trust boundaries, data sources      │
│     (Defines interface contracts and assumptions)                │
│                                                                  │
└──────────────────────────────────────────────────────────────────┘
```

#### Archetype-Specific Templates

Each software archetype loads default assertion templates that capture common requirements:

| Archetype | Default Assertions Loaded |
|-----------|---------------------------|
| **CLI Tool** | "Invalid args return non-zero exit code", "Help flag shows usage", "Stdout/stderr separation" |
| **Library** | "Public API is backwards-compatible", "No side effects without explicit opt-in", "Errors don't panic" |
| **Web Service** | "Unauthenticated requests rejected", "Invalid input returns 4xx", "Health endpoint exists" |
| **Data Pipeline** | "Failed records don't block pipeline", "Exactly-once or at-least-once semantics declared", "Schema validation at boundaries" |

These templates are *candidates*, not assumptions — the user reviews and refines each one.

#### Domain-Specific Invariants

Recognized domains load compliance and best-practice assertions:

| Domain | Loaded Assertions |
|--------|-------------------|
| **Finance** | "Monetary amounts use decimal, not float", "All transactions are auditable", "No negative balances without explicit overdraft" |
| **Healthcare** | "PII is encrypted at rest", "Access logging required", "Data retention policies enforced" |
| **Auth/Identity** | "Passwords never stored in plaintext", "Session tokens expire", "Failed logins are rate-limited" |
| **Multi-tenant** | "Tenant data isolation enforced", "No cross-tenant data leakage", "Tenant context required for all queries" |

#### Actor-Capability Matrix

The probing phase builds a matrix that drives use case enumeration:

```
                    │ Create │ Read │ Update │ Delete │ Special Actions
────────────────────┼────────┼──────┼────────┼────────┼─────────────────
Anonymous User      │   ─    │  ✓   │   ─    │   ─    │ Register, Login
Authenticated User  │   ✓    │  ✓   │  own   │  own   │ Logout, Export
Admin               │   ✓    │  ✓   │   ✓    │   ✓    │ Suspend, Audit
Background Job      │   ✓    │  ✓   │   ✓    │   ─    │ Cleanup, Notify
External API        │   ─    │  ✓   │   ─    │   ─    │ Webhook receive
```

Each cell becomes an assertion cluster:
- "✓" → happy path + error cases
- "own" → ownership constraints
- "─" → explicit denial (generates negative assertions)

#### Probing Output

The Domain Probing phase produces:

1. **Context Document**: Structured summary of archetype, domain, actors, boundaries
2. **Assertion Seed Set**: Pre-loaded assertions awaiting confirmation
3. **Use Case Skeleton**: Actor × Capability matrix with empty assertion slots
4. **Negative Constraints**: Explicit "this system does NOT..." statements

This output initializes the Interview Loop with meaningful starting assertions rather than a blank slate.

#### Example: Probing a Banking API

```
Probing Session:
────────────────
Q: What are you building?
A: Web service (REST API)
   → Loaded: 12 web service assertions

Q: What domain?
A: Finance / Banking
   → Loaded: 8 finance-specific assertions

Q: Who interacts with this system?
A: Account holders, Bank admins, External payment processor
   → Created 3 actor profiles

Q: What can Account holders do?
A: View balance, Transfer funds, View history, Update profile
   → Created 4 capability clusters

Q: What can this system NOT do?
A: Not handle cash deposits, Not process loans, Not multi-currency
   → Added 3 negative constraints

Q: Where are the boundaries?
A: Relies on external auth service, Calls payment processor API
   → Defined 2 interface contracts

Probing Complete. Seed assertions: 34
Beginning Interview Loop...
```

### The Interview Loop

```
┌──────────────────────────────────────────────────────────────────┐
│                        INTERVIEW LOOP                            │
│                                                                  │
│  1. User provides natural language input                         │
│     "I want a banking app where users can't overdraw"           │
│                                                                  │
│  2. LLM generates candidate assertions (batched)                 │
│     ┌────────────────────────────────────────────────────────┐  │
│     │ a) "Account balance is always >= 0" [Structure]        │  │
│     │ b) "Withdrawal requires amount <= balance" [Structure] │  │
│     │ c) "Failed withdrawals don't change balance" [Struct]  │  │
│     │ d) "Every withdrawal attempt gets a response" [Behav]  │  │
│     └────────────────────────────────────────────────────────┘  │
│                                                                  │
│  3. User provides feedback (free-form)                           │
│     a) ✓  b) ✓  c) "only for same-day withdrawals"  d) ✓        │
│                                                                  │
│  4. Free-form feedback triggers refinement                       │
│     c) User said "only for same-day withdrawals"                 │
│        → c1) "Same-day failed withdrawals don't change balance"  │
│        → c2) "Next-day withdrawals may incur pending state"      │
│        User confirms c1, elaborates on c2                        │
│                                                                  │
│  5. Parameterized assertions fill in concrete values             │
│     "Response arrives within <timeout> seconds"                  │
│     User specifies: 5                                            │
│                                                                  │
│  6. Confirmed assertions feed into formal models                 │
│     → Dafny: invariant balance >= 0                             │
│              requires amount <= balance                          │
│     → TLA+:  Response ~> (Success \/ Error)                     │
│              TemporalBound(Response, 5, "seconds")               │
│                                                                  │
│  7. Formal verification provides backpressure                    │
│     "These assertions are contradictory: X and Y"               │
│     "These assertions imply Z — confirm?"                        │
│                                                                  │
│  8. Loop until: use cases exhausted AND models consistent        │
│                                                                  │
└──────────────────────────────────────────────────────────────────┘
```

### Assertion Format

Assertions flow through three representations:

```
Natural Language     →    Intermediate Form    →    Formal Spec
─────────────────────────────────────────────────────────────────
"Balance can't go    →    {                    →    invariant
 negative"                  type: "invariant",       balance >= 0
                            entity: "Account",
                            property: "balance",
                            constraint: ">= 0"
                          }
```

The intermediate form enables:
- **Classification**: Route to Dafny vs TLA+ based on `type`
- **Composition**: Combine related assertions into coherent specs
- **Conflict detection**: Compare assertions before formal verification
- **Traceability**: Link generated code back to user confirmations

### Termination Conditions

The interview is complete when:

1. **Use case coverage**: Every enumerated use case has assertions covering its happy path and error cases
2. **Model consistency**: Dafny verifier and TLC find no contradictions
3. **Closure**: No new assertions are implied by existing ones (or all implied assertions are confirmed)
4. **Completeness signal**: User explicitly confirms "that's everything" for this scope

### Fresh Context Strategy

Like Ralph Wiggum, the Interview Engine uses fresh context windows:

- **Per-batch**: Each assertion generation batch starts with clean context + current formal specs
- **Specs as state**: Dafny/TLA+ files persist across context windows (like `IMPLEMENTATION_PLAN.md`)
- **Incremental verification**: Only re-verify affected portions when assertions change

## Bi-Directional Capability

### Forward: Intent → Software

1. Interview user to extract assertions
2. Build formal models (Structure via Dafny, Behavior via TLA+)
3. Check model consistency (Dafny verifier + TLC)
4. Generate code artifacts (Dafny extraction + supplementary code)
5. Verify generated code against models
6. Deploy and validate with E2E tests

### Reverse: Software → Intent

1. Parse existing codebase
2. Extract structure (types, schemas, validation logic, invariants)
3. Extract behavior (state machines, control flows, event handlers)
4. Synthesize Dafny spec from structure + constraints
5. Synthesize TLA+ spec from observed behavior
6. Generate human-readable assertions from formal models
7. Present to user for confirmation/correction

The reverse direction enables:
- **Documentation generation**: Produce accurate specs from legacy code
- **Migration assistance**: Understand existing system before rewriting
- **Verification**: Check if existing code matches stated requirements
- **Refactoring safety**: Know what invariants must be preserved

## Code Generation Strategy

The formal models (Dafny + TLA+) serve as the source of truth, but running software requires concrete code. This section defines what gets generated, how, and what remains hand-written.

### Generation Modes

The system supports three generation modes based on verification requirements:

| Mode | Description | Use When |
|------|-------------|----------|
| **Verified Extraction** | Dafny compiles directly to target language | Maximum correctness guarantees needed |
| **Spec-Guided Generation** | LLM generates code constrained by specs | Dafny extraction unavailable for target, or need idiomatic code |
| **Contract-First Development** | Generate contracts/interfaces only, human implements | Complex business logic, team prefers manual implementation |

### From Dafny: Verified Extraction

Dafny can compile verified code to multiple targets:

```
┌─────────────────────────────────────────────────────────────────┐
│                    DAFNY EXTRACTION TARGETS                     │
│                                                                 │
│  Dafny Source (.dfy)                                           │
│       │                                                         │
│       ├──► C#      (.cs)   ─── Best supported, production-ready│
│       ├──► Java    (.java) ─── Good support                    │
│       ├──► Go      (.go)   ─── Good support                    │
│       ├──► JavaScript (.js)─── Good support                    │
│       ├──► Python  (.py)   ─── Good support                    │
│       └──► Rust    (.rs)   ─── Community/experimental          │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**When to use**: Core domain logic where correctness is critical (financial calculations, access control, state transitions).

**Limitations**:
- Generated code may not be idiomatic
- Some Dafny features don't extract cleanly (unbounded integers, sets)
- External library integration requires careful FFI boundaries

### From TLA+: Behavioral Scaffolding

TLA+ doesn't generate executable code, but provides:

| Artifact | Generation Method |
|----------|-------------------|
| **State machine skeletons** | Extract states and transitions from TLA+ actions |
| **Test scenarios** | TLC traces become integration test sequences |
| **Invariant checks** | Runtime assertions from TLA+ invariants |
| **Concurrency guards** | Mutex/semaphore placement from mutual exclusion specs |

```
TLA+ Spec                         Generated Skeleton
───────────────                   ──────────────────
VARIABLES state, balance          interface StateMachine {
                                    state: State;
Init == state = "idle"              balance: number;
     /\ balance = 0               }

Deposit(amt) ==                   function deposit(amt: number) {
  /\ state = "idle"                 // PRECONDITION: state === "idle"
  /\ amt > 0                        // PRECONDITION: amt > 0
  /\ balance' = balance + amt       this.balance += amt;
  /\ state' = "idle"                // POSTCONDITION: state === "idle"
                                  }
```

### Spec-Guided LLM Generation

Dafny's direct compilation to target languages should be the **default choice** — it provides verified correctness guarantees that LLM generation cannot match.

#### Preferred Pattern: Dafny as Verified Core Library

For TypeScript projects, use Dafny-compiled JavaScript as a library:

```
┌─────────────────────────────────────────────────────────────────┐
│              DAFNY AS VERIFIED CORE LIBRARY                     │
│                                                                 │
│  1. Dafny source (verified)                                     │
│     account.dfy ──► dafny build --target:js ──► account.js     │
│                                                                 │
│  2. Generate type declarations (LLM or hand-written)            │
│     account.dfy ──► account.d.ts                                │
│                                                                 │
│  3. Consume in TypeScript                                       │
│     import { Account, withdraw } from './generated/account.js'; │
│                                                                 │
│  Result: Verified core + type-safe integration                  │
└─────────────────────────────────────────────────────────────────┘
```

The LLM's role shrinks to generating:
- **Type declarations** (`.d.ts`) for Dafny-compiled JS
- **Glue code** wiring the verified core to frameworks (Express routes, React hooks)
- **Validation schemas** (Zod) that mirror Dafny preconditions at API boundaries

#### When Full LLM Generation Is Warranted

Reserve LLM code generation for cases where Dafny extraction truly doesn't apply:

| Reason | Example |
|--------|---------|
| **Unsupported target** | Rust, Swift, Kotlin, or domain-specific languages |
| **Framework-native code** | React components, database migrations, CLI argument parsing |
| **Performance-critical paths** | When Dafny's runtime overhead is unacceptable |

When LLM generation is warranted, the formal specs act as constraints:

```
┌──────────────────────────────────────────────────────────────────┐
│                   SPEC-GUIDED GENERATION                         │
│                                                                  │
│  Input to LLM:                                                   │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │ Dafny Contract:                                            │ │
│  │   method Withdraw(amount: int) returns (success: bool)     │ │
│  │     requires amount > 0                                     │ │
│  │     requires amount <= balance                              │ │
│  │     ensures success ==> balance == old(balance) - amount   │ │
│  │     ensures !success ==> balance == old(balance)           │ │
│  │                                                            │ │
│  │ Target: TypeScript with Zod validation                     │ │
│  │ Style: Functional, immutable updates                       │ │
│  └────────────────────────────────────────────────────────────┘ │
│                                                                  │
│  Output from LLM:                                                │
│  ┌────────────────────────────────────────────────────────────┐ │
│  │ const WithdrawInput = z.object({                           │ │
│  │   amount: z.number().positive()                            │ │
│  │ });                                                        │ │
│  │                                                            │ │
│  │ function withdraw(account: Account, input: WithdrawInput)  │ │
│  │   : Result<Account, WithdrawError> {                       │ │
│  │   const { amount } = WithdrawInput.parse(input);           │ │
│  │   if (amount > account.balance) {                          │ │
│  │     return Err({ code: 'INSUFFICIENT_FUNDS' });            │ │
│  │   }                                                        │ │
│  │   return Ok({ ...account, balance: account.balance - amt });│ │
│  │ }                                                          │ │
│  └────────────────────────────────────────────────────────────┘ │
│                                                                  │
│  Verification:                                                   │
│  • Generated property-based tests exercise pre/postconditions   │
│  • Runtime validation enforces Dafny requires clauses           │
│  • Type system approximates refinement types where possible      │
│                                                                  │
└──────────────────────────────────────────────────────────────────┘
```

### Layer-by-Layer Generation Strategy

| Layer | What's Generated | From Which Spec | Verification |
|-------|------------------|-----------------|--------------|
| **Types & Schemas** | Type definitions, Zod schemas, DB schemas | Dafny classes + refinement types | Type-checker + property tests |
| **Validation** | Input validators, guards, constraint checks | Dafny `requires` clauses | Unit tests from counterexamples |
| **Domain Logic** | Core business functions | Dafny `method` bodies (extracted or LLM) | Property-based tests from contracts |
| **State Machines** | State transition handlers | TLA+ actions | Integration tests from TLC traces |
| **API Layer** | Route handlers, request/response shapes | Dafny contracts + archetype templates | Contract tests |
| **Infrastructure** | Config, deployment manifests | Requirements + archetype | E2E smoke tests |

### What Remains Hand-Written

Not everything should be generated. The system explicitly defers:

| Category | Reason | Guidance Provided |
|----------|--------|-------------------|
| **UI/UX implementation** | Highly creative, hard to specify formally | Component interfaces from data contracts |
| **Performance optimizations** | Require profiling, not specification | Algorithmic complexity bounds from specs |
| **Third-party integrations** | External API behavior isn't formally modeled | Interface contracts, mock implementations |
| **Deployment specifics** | Environment-dependent, operational concerns | Infrastructure requirements from NFRs |

### Generation Traceability

Every generated artifact links back to its source assertions:

```typescript
/**
 * @generated
 * @source-assertion A-047: "Account balance never negative"
 * @source-spec structure.dfy:45-48
 * @verified 2024-01-15T10:30:00Z
 */
const BalanceSchema = z.number().nonnegative();

/**
 * @generated
 * @source-assertion A-052: "Withdrawal requires sufficient funds"
 * @source-assertion A-053: "Failed withdrawal doesn't change balance"
 * @source-spec structure.dfy:62-71
 * @verified 2024-01-15T10:30:00Z
 */
function withdraw(account: Account, amount: number): Result<Account, Error> {
  // ...
}
```

This enables:
- **Impact analysis**: When an assertion changes, find all affected code
- **Audit trails**: Prove generated code satisfies requirements
- **Regeneration**: Update specific artifacts when specs change

### Incremental Regeneration

When assertions or specs change:

```
┌─────────────────────────────────────────────────────────────────┐
│                  INCREMENTAL REGENERATION                       │
│                                                                 │
│  1. Assertion A-047 modified: "balance >= 0" → "balance >= -100"│
│                                                                 │
│  2. Dependency analysis:                                        │
│     A-047 ──► structure.dfy (Account.balance invariant)        │
│           ──► BalanceSchema (Zod validator)                    │
│           ──► withdraw() (uses balance constraint)             │
│           ──► Account.test.ts (property tests)                 │
│                                                                 │
│  3. Regenerate affected artifacts only                          │
│                                                                 │
│  4. Re-verify:                                                  │
│     ✓ Dafny verifier passes                                    │
│     ✓ Property tests pass                                       │
│     ✗ Integration test fails (downstream expects >= 0)         │
│                                                                 │
│  5. Surface conflict to user for resolution                     │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Tools

| Tool | Role |
|------|------|
| **Dafny** | Structure model: refinement types, contracts, invariants, verified code extraction (Z3 backend) |
| **TLA+/TLC** | Behavior model: temporal properties, state exploration, counterexample generation |
| **Playwright** | Runtime validation: E2E tests, user journey verification |

## Software Archetypes

The two-model approach applies across software types, but emphasis shifts:

| Archetype | Structure Focus | Behavior Focus | Typical Persistence |
|-----------|-----------------|----------------|---------------------|
| **Library/SDK** | API types, versioning contracts | Stateless transforms, error handling | None |
| **CLI Tool** | Arg schemas, config formats | Command execution, I/O patterns | Files, config |
| **Web Service** | API contracts, data schemas | Request lifecycle, auth flows | Database, cache |
| **Compiler/Interpreter** | AST, IR, target formats | Parse → Transform → Emit pipeline | None or temp files |
| **Desktop App** | UI state, document formats | User interactions, undo/redo | Local files, preferences |
| **Game** | Entity types, asset formats | Game loop, physics, AI behaviors | Save files, leaderboards |
| **Data Pipeline** | Input/output schemas, stage contracts | Transform DAG, error recovery | Various sources/sinks |
| **Embedded System** | Register maps, protocol definitions | Interrupt handlers, state machines | Flash, EEPROM |

## Key Insights

### 1. Recognition Over Recall
Users are faster at reviewing and refining proposed assertions than articulating requirements from scratch. The LLM generates candidates; the human provides feedback — confirming, denying, or offering refinements the agent might not have considered.

### 2. Parameterized Discovery
Discovery uses typed parameters to collapse infinite search spaces:
```
"Rate limit is <uint> per <sec|min|hour>" → User specifies: 100, minute
```

### 3. The Curry-Howard Connection
Assertions are types. Confirmed assertions are inhabited types. Code satisfying assertions is a program that type-checks. This activates decades of PL research.

### 4. Use Cases Define Completeness
The system is fully specified when all intended use cases are enumerated, decomposed into steps, and each step has assertions. For CLI tools, these are command invocations. For libraries, these are API call sequences. For web apps, these are user journeys. Tests are executable use case specifications.

### 5. Verification at Every Layer
The formal models aren't documentation — they're oracles. Every generated artifact can be checked against the spec.

## Success Criteria

The plugin succeeds when:

1. A user can describe software in natural language and receive a working, correct implementation
2. The generated software provably satisfies stated requirements (via formal verification where possible, testing elsewhere)
3. Given existing software, the plugin can extract and present the implicit specification
4. Contradictions in requirements are caught *before* code is written
5. Edge cases and failure modes are systematically explored, not forgotten
6. Environment configuration (Nix, Docker, dependencies, etc.) is derived from requirements when needed, not manually configured

## Open Research Questions

1. **Assertion generation quality**: How do we ensure the LLM generates the *right* assertions? Missing critical assertions is worse than asking unnecessary ones.

2. **Model synchronization**: How do we propagate changes between models efficiently? When a Dafny contract changes, what TLA+ specs must be updated?

3. **Reverse engineering fidelity**: How accurately can we recover intent from code? What's lost in translation?

4. **Incremental verification**: As the system grows, how do we avoid re-checking everything? What's the minimal re-verification after a change?

5. **Practical TLA+ integration**: TLA+ is powerful but has a learning curve. How do we hide complexity while preserving power?

6. **Scalability**: Can this approach work for large systems? Where are the limits?
