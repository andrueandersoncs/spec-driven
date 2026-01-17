---
name: domain-templates
description: This skill should be used when identifying application domains, loading domain-specific assertions, handling compliance requirements, or when the user asks "this is a finance app", "load healthcare assertions", "what domain constraints apply", "add auth domain", "this handles payments", "what compliance rules apply", "load multi-tenant assertions", "add e-commerce domain", "what real-time constraints should I add", or describes domain-specific requirements like HIPAA, PCI, SOX, or financial regulations.
version: 0.1.0
---

# Domain Templates

Load domain-specific assertions and compliance requirements.

## Domain Identification

Domains overlay on top of archetypes, adding specialized constraints.

| Domain | Key Concerns | Typical Archetypes |
|--------|--------------|-------------------|
| Finance | Money precision, audit, transactions | Web Service, Library |
| Healthcare | PII, HIPAA, data retention | Web Service, Data Pipeline |
| Auth/Identity | Credentials, sessions, tokens | Library, Web Service |
| Multi-tenant | Isolation, tenant context | Web Service, Data Pipeline |
| E-commerce | Inventory, payments, orders | Web Service |
| Real-time | Latency, ordering, delivery | Web Service, Library |

## Finance Domain

Assertions for financial applications.

### Structure (Dafny)

```
A-FIN-001: Monetary amounts use decimal, not float
A-FIN-002: Currency explicitly tracked with amounts
A-FIN-003: All transactions are immutable records
A-FIN-004: Audit trail for all state changes
A-FIN-005: No negative balances without explicit overdraft
A-FIN-006: Exchange rates timestamped
A-FIN-007: Rounding rules explicit and consistent
```

### Behavior (TLA+)

```
A-FIN-008: Double-entry bookkeeping (debits = credits)
A-FIN-009: Transactions are atomic
A-FIN-010: Failed transactions fully roll back
A-FIN-011: Concurrent access to same account serialized
A-FIN-012: Settlement eventually completes
```

### Compliance Notes

- SOX: Audit trail requirements
- PCI-DSS: Card data handling (if applicable)
- AML: Transaction monitoring thresholds

## Healthcare Domain

Assertions for health data applications.

### Structure (Dafny)

```
A-HEALTH-001: PII fields identified and marked
A-HEALTH-002: PHI encrypted at rest
A-HEALTH-003: Access control per data category
A-HEALTH-004: Data retention periods enforced
A-HEALTH-005: Consent tracked with data
A-HEALTH-006: Anonymization preserves utility
```

### Behavior (TLA+)

```
A-HEALTH-007: All data access logged
A-HEALTH-008: Access denied without valid authorization
A-HEALTH-009: Data deletion completes within policy window
A-HEALTH-010: Breach detection within threshold
```

### Compliance Notes

- HIPAA: PHI handling, minimum necessary
- HITECH: Breach notification
- GDPR: If EU patients involved

## Auth/Identity Domain

Assertions for authentication and authorization.

### Structure (Dafny)

```
A-AUTH-001: Passwords never stored in plaintext
A-AUTH-002: Password hash uses approved algorithm (bcrypt, argon2)
A-AUTH-003: Session tokens cryptographically random
A-AUTH-004: Token expiration explicitly set
A-AUTH-005: Permissions are explicit, not implied
A-AUTH-006: Role hierarchy well-defined
```

### Behavior (TLA+)

```
A-AUTH-007: Login creates new session
A-AUTH-008: Logout invalidates session
A-AUTH-009: Session expires after inactivity
A-AUTH-010: Failed logins trigger rate limiting
A-AUTH-011: Password reset invalidates old password
A-AUTH-012: MFA required for sensitive operations
```

### Security Notes

- OWASP: Authentication best practices
- NIST: Password guidelines (800-63B)
- Consider: Credential stuffing, session fixation

## Multi-tenant Domain

Assertions for SaaS and shared infrastructure.

### Structure (Dafny)

```
A-TENANT-001: All data has tenant_id
A-TENANT-002: Tenant context required for all queries
A-TENANT-003: Cross-tenant references prohibited
A-TENANT-004: Tenant-specific configuration isolated
A-TENANT-005: Resource quotas per tenant defined
```

### Behavior (TLA+)

```
A-TENANT-006: Query results filtered by tenant
A-TENANT-007: No data leakage across tenants
A-TENANT-008: Tenant deletion removes all data
A-TENANT-009: Tenant operations isolated (no noisy neighbor)
A-TENANT-010: Billing events attributed to tenant
```

### Architecture Notes

- Row-level vs schema-level isolation
- Shared vs dedicated compute
- Data residency requirements

## E-commerce Domain

Assertions for online retail applications.

### Structure (Dafny)

```
A-ECOM-001: Inventory quantity non-negative
A-ECOM-002: Price includes currency
A-ECOM-003: Order total = sum(items) + tax + shipping - discounts
A-ECOM-004: SKU uniquely identifies product variant
A-ECOM-005: Cart belongs to session or user
```

### Behavior (TLA+)

```
A-ECOM-006: Stock decremented atomically on purchase
A-ECOM-007: Oversell prevented (or explicitly allowed)
A-ECOM-008: Payment before fulfillment
A-ECOM-009: Order state machine: cart → checkout → paid → shipped → delivered
A-ECOM-010: Abandoned cart recovery within window
A-ECOM-011: Refund restores inventory (if applicable)
```

## Real-time Domain

Assertions for low-latency and streaming applications.

### Structure (Dafny)

```
A-RT-001: Message format versioned
A-RT-002: Sequence numbers track ordering
A-RT-003: Timestamps use consistent clock source
A-RT-004: Buffer sizes bounded
```

### Behavior (TLA+)

```
A-RT-005: Messages delivered in order (per channel)
A-RT-006: Acknowledgment within timeout
A-RT-007: Reconnection resumes from last ack
A-RT-008: Backpressure when consumer slow
A-RT-009: Heartbeat detects connection loss
A-RT-010: Graceful degradation under load
```

## Combining Domains

Projects often span multiple domains:

```
E-commerce + Finance + Auth
├── A-ECOM-* (product, cart, order)
├── A-FIN-* (payment, refund, ledger)
└── A-AUTH-* (login, session, permissions)
```

Load all applicable domains, then deduplicate and resolve conflicts.

### Conflict Resolution

When domains overlap:
1. More restrictive assertion wins
2. Compliance requirements override preferences
3. Surface conflicts to user for explicit decision

## Using Templates

### Loading Process

1. Identify applicable domains (may be multiple)
2. Load domain assertion sets
3. Merge with archetype assertions
4. Deduplicate equivalent assertions
5. Present combined set to user

### Assertion Layering

```
Base Layer:     Archetype assertions (CLI, Web Service, etc.)
Domain Layer:   Domain assertions (Finance, Auth, etc.)
Custom Layer:   User-specific assertions
```

Each layer can:
- Add new assertions
- Strengthen existing assertions
- Override defaults with user confirmation

## Additional Resources

### Example Files
- **`examples/finance-domain-assertions.json`** - Complete finance domain assertion set in JSON format
- **`examples/auth-domain-assertions.json`** - Complete auth domain assertion set in JSON format

### Related Skills
- `archetype-templates` - Base layer assertions
- `assertion-taxonomy` - Classification for custom assertions
