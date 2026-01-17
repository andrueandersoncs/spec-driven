# Assertion Manifest Format

The `specs/assertions.json` file is the central manifest that tracks all assertions, their status, and metadata for the specification-driven development workflow.

## Schema

```json
{
  "version": "1.0.0",
  "archetype": "web-service",
  "domains": ["finance", "auth"],
  "actors": ["customer", "admin", "background-job"],
  "capabilities": {
    "customer": ["view-balance", "transfer", "view-history"],
    "admin": ["suspend-account", "audit", "override-limits"]
  },
  "boundaries": ["external-payment-processor", "auth-service"],
  "constraints": ["not-multi-currency", "not-real-time"],
  "assertions": [...],
  "metadata": {
    "created": "2024-01-15T10:00:00Z",
    "lastModified": "2024-01-15T14:30:00Z",
    "lastVerified": "2024-01-15T14:25:00Z"
  }
}
```

## Field Reference

### Top-Level Fields

| Field | Type | Description |
|-------|------|-------------|
| `version` | string | Manifest schema version (semantic versioning) |
| `archetype` | string | Software archetype (cli-tool, library, web-service, etc.) |
| `domains` | string[] | Applicable domains (finance, healthcare, auth, etc.) |
| `actors` | string[] | Who/what interacts with the system |
| `capabilities` | object | Actor-to-capabilities mapping |
| `boundaries` | string[] | External dependencies and trust boundaries |
| `constraints` | string[] | What the system explicitly is NOT |
| `assertions` | Assertion[] | Array of assertion objects |
| `metadata` | object | Timestamps and tracking info |

### Assertion Object

Each assertion in the `assertions` array follows this structure:

```json
{
  "id": "A-001",
  "natural": "Account balance never goes negative",
  "type": "invariant",
  "category": "structure",
  "entity": "Account",
  "property": "balance",
  "constraint": ">= 0",
  "status": "confirmed",
  "source": "user-interview-001",
  "formalSpec": {
    "file": "specs/dafny/structure.dfy",
    "lines": "45-48"
  },
  "dependencies": [],
  "refinedFrom": null,
  "tags": ["critical", "finance"]
}
```

### Assertion Fields

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | Unique identifier (A-XXX format) |
| `natural` | string | Yes | Natural language statement |
| `type` | string | Yes | Assertion type (see types below) |
| `category` | string | Yes | `structure` or `behavior` |
| `entity` | string | No | Entity this assertion applies to |
| `property` | string | No | Property being constrained |
| `constraint` | string | No | The constraint expression |
| `status` | string | Yes | Current status (see statuses below) |
| `source` | string | Yes | Where this assertion came from |
| `formalSpec` | object | No | Link to formal specification |
| `dependencies` | string[] | No | IDs of assertions this depends on |
| `refinedFrom` | string | No | ID of assertion this refines |
| `tags` | string[] | No | Custom tags for filtering |

### Assertion Types

#### Structure Types (→ Dafny)

| Type | Description | Dafny Construct |
|------|-------------|-----------------|
| `data-constraint` | Constrains data values | Refinement type |
| `invariant` | Entity state constraint | `invariant` clause |
| `precondition` | Operation input requirement | `requires` clause |
| `postcondition` | Operation output guarantee | `ensures` clause |
| `relationship` | Entity relationship constraint | References, predicates |
| `uniqueness` | Uniqueness constraint | Predicate over collection |

#### Behavior Types (→ TLA+)

| Type | Description | TLA+ Construct |
|------|-------------|----------------|
| `liveness` | Something eventually happens | `~>` (leads-to) |
| `safety` | Something never happens | `[][...]_vars` |
| `ordering` | Sequence constraint | Prefix, ordering operators |
| `fairness` | Progress guarantee | `WF_vars`, `SF_vars` |
| `reachability` | State is reachable | `<>[]`, `[]<>` |
| `mutual-exclusion` | Concurrent access constraint | Cardinality constraints |

### Assertion Statuses

| Status | Description |
|--------|-------------|
| `pending` | Proposed but not yet reviewed |
| `confirmed` | User confirmed as correct |
| `denied` | User rejected as incorrect |
| `refined` | Replaced by a refined version |
| `deferred` | Acknowledged but deferred for later |
| `inferred` | Extracted from existing code |

### Source Types

The `source` field indicates where an assertion originated:

| Source Pattern | Description |
|----------------|-------------|
| `user-interview-XXX` | From interview session |
| `archetype-{name}` | From archetype template |
| `domain-{name}` | From domain template |
| `reverse-engineer` | Extracted from code |
| `implied-by-{id}` | Implied by another assertion |
| `verification-failure` | Created to resolve conflict |

## Example: Complete Manifest

```json
{
  "version": "1.0.0",
  "archetype": "web-service",
  "domains": ["finance"],
  "actors": ["customer", "admin"],
  "capabilities": {
    "customer": ["view-balance", "deposit", "withdraw", "transfer"],
    "admin": ["suspend-account", "view-audit-log"]
  },
  "boundaries": ["external-payment-processor"],
  "constraints": ["not-multi-currency", "not-real-time-trading"],
  "assertions": [
    {
      "id": "A-001",
      "natural": "Account balance never goes negative",
      "type": "invariant",
      "category": "structure",
      "entity": "Account",
      "property": "balance",
      "constraint": ">= 0",
      "status": "confirmed",
      "source": "domain-finance",
      "formalSpec": {
        "file": "specs/dafny/structure.dfy",
        "lines": "15-16"
      },
      "dependencies": [],
      "tags": ["critical"]
    },
    {
      "id": "A-002",
      "natural": "Can only withdraw if sufficient funds exist",
      "type": "precondition",
      "category": "structure",
      "entity": "Account",
      "property": "withdraw",
      "constraint": "amount <= balance",
      "status": "confirmed",
      "source": "user-interview-001",
      "formalSpec": {
        "file": "specs/dafny/structure.dfy",
        "lines": "25-26"
      },
      "dependencies": ["A-001"],
      "tags": []
    },
    {
      "id": "A-003",
      "natural": "Every transfer eventually completes or is cancelled",
      "type": "liveness",
      "category": "behavior",
      "entity": "Transfer",
      "status": "confirmed",
      "source": "user-interview-001",
      "formalSpec": {
        "file": "specs/tla/behavior.tla",
        "lines": "45-47"
      },
      "dependencies": [],
      "tags": []
    },
    {
      "id": "A-004",
      "natural": "Never process the same payment twice",
      "type": "safety",
      "category": "behavior",
      "entity": "Payment",
      "status": "confirmed",
      "source": "domain-finance",
      "formalSpec": {
        "file": "specs/tla/behavior.tla",
        "lines": "52-54"
      },
      "dependencies": [],
      "tags": ["critical"]
    }
  ],
  "metadata": {
    "created": "2024-01-15T10:00:00Z",
    "lastModified": "2024-01-15T14:30:00Z",
    "lastVerified": "2024-01-15T14:25:00Z"
  }
}
```

## Working with the Manifest

### Adding Assertions

When adding a new assertion:

1. Generate unique ID (next available A-XXX)
2. Set `status` to `pending`
3. Set `source` to indicate origin
4. Leave `formalSpec` empty until spec is generated

### Confirming Assertions

When user confirms an assertion:

1. Update `status` to `confirmed`
2. Generate formal spec (Dafny or TLA+)
3. Update `formalSpec` with file and line references
4. Update `metadata.lastModified`

### Refining Assertions

When refining an existing assertion:

1. Create new assertion with new ID
2. Set `refinedFrom` to original assertion ID
3. Update original assertion's `status` to `refined`
4. Add note about refinement in original

### Tracking Verification

After running verification:

1. Update `metadata.lastVerified` timestamp
2. If verification fails, create conflict assertions
3. Link conflict assertions to involved assertions via `dependencies`

## Integration with Commands

| Command | Manifest Operations |
|---------|---------------------|
| `/probe-domain` | Creates manifest, sets archetype/domains/actors |
| `/interview` | Adds assertions, updates statuses |
| `/verify` | Updates lastVerified, may add conflict assertions |
| `/generate` | Reads confirmed assertions for code generation |
| `/reverse-engineer` | Adds assertions with `inferred` status |
| `/show-spec` | Reads and displays manifest state |
| `/resolve-conflict` | Updates assertion statuses and dependencies |
