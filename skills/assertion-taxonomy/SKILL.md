---
name: assertion-taxonomy
description: This skill should be used when classifying user requirements into formal assertions, determining whether an assertion is "structural" (Dafny) or "behavioral" (TLA+), categorizing assertions by type (invariant, precondition, postcondition, liveness, safety, etc.), or when the user asks "is this a Dafny or TLA+ assertion", "what type of assertion is this", "classify this requirement", "route this to the right model", "which model should I use for this", "help me decide between Dafny and TLA+", "categorize this spec", or "is this structure or behavior".
version: 0.1.0
---

# Assertion Taxonomy

Classify user intent into formal assertions and route them to the appropriate verification model.

## Core Principle: Space vs. Time

The fundamental distinction determines routing:

| Dimension | Question | Model | Formalism |
|-----------|----------|-------|-----------|
| **Space** | What is true at a single moment? | Dafny | Refinement types, contracts, invariants |
| **Time** | What is true across sequences of states? | TLA+ | Temporal logic, state machines |

## Classification Decision Tree

Apply this heuristic to classify any requirement:

```
Is this about a SINGLE moment in time, or SEQUENCES of states?
├── Single moment → Dafny (Structure)
│   ├── About data shape/type? → refinement type
│   ├── About entity state? → class invariant
│   ├── About operation input? → requires (precondition)
│   └── About operation output? → ensures (postcondition)
│
└── Sequences of states → TLA+ (Behavior)
    ├── "Eventually X happens" → liveness
    ├── "X never happens" → safety
    ├── "X before Y" → ordering
    └── "X and Y don't overlap" → mutual exclusion
```

## Classify Structure Assertions (Route to Dafny)

Identify and route assertions that constrain what is true at any single point in time.

### Data Constraint
**Pattern**: "X must be/have Y"
**Examples**:
- "User age must be positive" → `type Age = x: int | x > 0`
- "Email must contain @" → `predicate ValidEmail(s: string)`

### Entity Invariant
**Pattern**: "X is always Y" (for entity state)
**Examples**:
- "Account balance never negative" → `ghost predicate Valid() { balance >= 0 }`
- "Order total equals sum of items" → `ghost predicate Valid() { total == SumItems(items) }`

**Note**: In Dafny, class invariants are expressed using `Valid()` predicates (see [Dafny Reference Manual](https://dafny.org/latest/DafnyRef/DafnyRef#sec-class-types)).

### Precondition
**Pattern**: "Can only X if Y" / "X requires Y"
**Examples**:
- "Can only withdraw if sufficient funds" → `requires amount <= balance`
- "Delete requires ownership" → `requires caller == owner`

### Postcondition
**Pattern**: "After X, Y is true" / "X results in Y"
**Examples**:
- "Deposit increases balance by exact amount" → `ensures balance == old(balance) + amount`
- "Sort produces ordered output" → `ensures Sorted(result)`

### Relationship
**Pattern**: "Every X has/belongs to Y"
**Examples**:
- "Every order belongs to one customer" → non-null reference
- "User has at most one active session" → uniqueness constraint

### Uniqueness
**Pattern**: "X is unique across Y"
**Examples**:
- "Email addresses unique across users" → `predicate UniqueEmails(users: set<User>)`

## Classify Behavior Assertions (Route to TLA+)

Identify and route assertions that constrain sequences of states over time. See the [TLA+ Repository](https://github.com/tlaplus/tlaplus) for tools and the [TLA+ Examples](https://github.com/tlaplus/Examples) for reference specifications.

### Liveness
**Pattern**: "Eventually X" / "X leads to Y"
**Examples**:
- "Every request gets a response" → `Request ~> Response`
- "Pending orders eventually complete" → `Pending ~> Complete`

### Safety
**Pattern**: "Never X" / "X doesn't happen"
**Examples**:
- "Never process payment twice" → `[][~(ProcessPayment /\ processed)]_vars`
- "Never access after logout" → safety property

### Ordering
**Pattern**: "X before Y" / "X must precede Y"
**Examples**:
- "Auth before API calls" → `Auth ∈ prefix(APICall)`
- "Validate before save" → ordering constraint

### Fairness
**Pattern**: "No X starves" / "X gets turn"
**Examples**:
- "No request starves" → `WF_vars(ProcessRequest)`
- "All threads eventually run" → weak fairness

### Reachability
**Pattern**: "Can always reach X" / "X is reachable"
**Examples**:
- "Can always return to idle" → `Spec => <>[]Idle`
- "Recovery state reachable" → reachability property

### Mutual Exclusion
**Pattern**: "Only one X at a time" / "X and Y don't overlap"
**Examples**:
- "At most one writer" → `Cardinality(writers) <= 1`
- "Locks are exclusive" → mutual exclusion

## Create Intermediate Representation

Transform natural language to structured form before generating formal specs:

```json
{
  "id": "A-001",
  "natural": "Account balance never negative",
  "type": "invariant",
  "category": "structure",
  "entity": "Account",
  "property": "balance",
  "constraint": ">= 0",
  "status": "confirmed",
  "source": "user-interview-001"
}
```

This enables:
- **Classification**: Route based on `category`
- **Composition**: Group by `entity`
- **Traceability**: Link to `source`
- **Conflict detection**: Compare constraints

## Handle Ambiguous Cases

When requirements could go either way, apply these tiebreakers:

| Indicator | Route To |
|-----------|----------|
| "at any point" / "always true" | Dafny invariant |
| "eventually" / "leads to" | TLA+ liveness |
| "within N seconds/attempts" | TLA+ temporal bound |
| Single operation contract | Dafny pre/post |
| Multi-step workflow | TLA+ behavior |
| Data validation | Dafny refinement |
| Concurrency control | TLA+ mutual exclusion |

When genuinely ambiguous, ask the user:
> "Is this about what's true at each moment (→ Dafny), or about how the system evolves over time (→ TLA+)?"

## Verify Cross-Model Consistency

When both models exist, check consistency between them:

1. Every TLA+ action should preserve Dafny invariants
2. Every Dafny method should have a TLA+ action counterpart
3. Reachable TLA+ states should satisfy Dafny constraints

## Additional Resources

### Reference Files
- **`references/classification-examples.md`** - Extended examples for each assertion category
- **`references/assertion-manifest-format.md`** - Complete schema for `specs/assertions.json` manifest

### External Resources

**TLA+ (Behavior)**:
| Resource | Description |
|----------|-------------|
| [TLA+ Repository](https://github.com/tlaplus/tlaplus) | Official TLA+ tools (TLC, SANY, PlusCal) |
| [TLA+ Examples](https://github.com/tlaplus/Examples) | Curated specifications including Paxos, Raft, Two-Phase Commit |
| [TLA+ Cheatsheet](https://lamport.azurewebsites.net/tla/summary-standalone.pdf) | Quick reference for operators and syntax |
| [Learn TLA+](https://learntla.com/) | Interactive tutorial |

**Dafny (Structure)**:
| Resource | Description |
|----------|-------------|
| [Dafny Repository](https://github.com/dafny-lang/dafny) | Official Dafny verification language |
| [Dafny Reference Manual](https://dafny.org/latest/DafnyRef/DafnyRef) | Complete language reference |

### Workflow Integration

After classification:
1. Generate intermediate representation
2. Add to `specs/assertions.json` manifest
3. Generate appropriate formal spec (Dafny or TLA+)
4. Run verification
5. Surface conflicts if any
