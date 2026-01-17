# Classification Examples

Extended examples demonstrating assertion classification for each category.

## Structure Assertions (Dafny)

### Data Constraints

| Natural Language | Classification | Dafny |
|-----------------|----------------|-------|
| "Age must be between 0 and 150" | refinement type | `type Age = x: int \| 0 <= x <= 150` |
| "Price is non-negative decimal" | refinement type | `type Price = x: real \| x >= 0.0` |
| "Username is 3-20 alphanumeric chars" | predicate | `predicate ValidUsername(s: string)` |
| "Email matches pattern X" | predicate | `predicate ValidEmail(s: string)` |
| "Quantity is positive integer" | refinement type | `type Quantity = x: int \| x > 0` |
| "Status is one of: pending, active, closed" | enum | `datatype Status = Pending \| Active \| Closed` |

### Entity Invariants

In Dafny, class invariants are expressed using `Valid()` predicates. See [Dafny Reference Manual](https://dafny.org/latest/DafnyRef/DafnyRef#sec-class-types).

| Natural Language | Classification | Dafny Valid() predicate |
|-----------------|----------------|-------------------------|
| "Account balance never negative" | invariant | `ghost predicate Valid() { balance >= 0 }` |
| "Cart total equals sum of item prices" | invariant | `ghost predicate Valid() { total == Sum(items) }` |
| "User always has valid email" | invariant | `ghost predicate Valid() { ValidEmail(email) }` |
| "Order items list is never empty" | invariant | `ghost predicate Valid() { \|items\| > 0 }` |
| "Session token is non-empty when logged in" | invariant | `ghost predicate Valid() { loggedIn ==> token != "" }` |
| "Audit trail is append-only" | invariant | (use ghost history variable in method postconditions) |

### Preconditions

| Natural Language | Classification | Dafny |
|-----------------|----------------|-------|
| "Can withdraw only if balance sufficient" | requires | `requires amount <= balance` |
| "Can delete only own resources" | requires | `requires caller == owner` |
| "Can only checkout with items in cart" | requires | `requires \|cart.items\| > 0` |
| "Transfer requires different accounts" | requires | `requires from != to` |
| "Can only approve pending requests" | requires | `requires request.status == Pending` |
| "Update requires authentication" | requires | `requires IsAuthenticated(session)` |

### Postconditions

| Natural Language | Classification | Dafny |
|-----------------|----------------|-------|
| "Deposit increases balance by exact amount" | ensures | `ensures balance == old(balance) + amount` |
| "Delete removes exactly one item" | ensures | `ensures \|items\| == old(\|items\|) - 1` |
| "Sort produces ordered output" | ensures | `ensures Sorted(result)` |
| "Search returns subset of input" | ensures | `ensures result <= input` |
| "Create returns new ID" | ensures | `ensures result !in old(ids)` |
| "Inverse operation restores original" | ensures | `ensures Decrypt(Encrypt(x)) == x` |

### Relationships

| Natural Language | Classification | Dafny |
|-----------------|----------------|-------|
| "Every order belongs to one customer" | reference | `var customer: Customer` (non-null) |
| "User can have multiple addresses" | collection | `var addresses: seq<Address>` |
| "Product belongs to one category" | reference | `var category: Category` |
| "Comment references parent post" | reference | `var post: Post` |
| "Session associated with exactly one user" | 1:1 | `var user: User` |

### Uniqueness

| Natural Language | Classification | Dafny |
|-----------------|----------------|-------|
| "Email unique across users" | predicate | `predicate UniqueEmails(users: set<User>)` |
| "Order number unique" | predicate | `predicate UniqueOrderNumbers(orders: set<Order>)` |
| "Username unique case-insensitive" | predicate | `predicate UniqueLowerUsernames(users: set<User>)` |
| "SKU unique per product" | predicate | `predicate UniqueSKUs(products: set<Product>)` |

## Behavior Assertions (TLA+)

### Liveness

| Natural Language | Classification | TLA+ |
|-----------------|----------------|------|
| "Every request gets a response" | leads-to | `Request ~> Response` |
| "Pending orders eventually complete" | leads-to | `Pending ~> (Complete \/ Cancelled)` |
| "Submitted jobs eventually run" | leads-to | `Submitted ~> Running` |
| "Messages are eventually delivered" | leads-to | `Sent ~> Delivered` |
| "Locks are eventually released" | leads-to | `Held ~> Released` |
| "Errors are eventually handled" | leads-to | `Error ~> (Recovered \/ Reported)` |

### Safety

| Natural Language | Classification | TLA+ |
|-----------------|----------------|------|
| "Never process payment twice" | safety | `[][~(ProcessPayment /\ paid)]_vars` |
| "Never delete without backup" | safety | `[][Delete => backed_up]_vars` |
| "Never exceed rate limit" | safety | `[][requests_in_window <= limit]_vars` |
| "Never expose PII unencrypted" | safety | `[][~(Send /\ pii /\ ~encrypted)]_vars` |
| "Never allow unauthorized access" | safety | `[][Access => Authorized]_vars` |
| "Never corrupt data during migration" | safety | `[][Migrate => DataIntact]_vars` |

### Ordering

| Natural Language | Classification | TLA+ |
|-----------------|----------------|------|
| "Auth before any API call" | prefix | `Auth \in prefix(APICall)` |
| "Validate before save" | ordering | `Validate -< Save` |
| "Pay before ship" | ordering | `Payment -< Shipment` |
| "Review before publish" | ordering | `Review -< Publish` |
| "Create before update" | ordering | `Create -< Update` |
| "Init before any operation" | prefix | `Init \in prefix(Operation)` |

### Fairness

| Natural Language | Classification | TLA+ |
|-----------------|----------------|------|
| "No request starves" | weak fairness | `WF_vars(ProcessRequest)` |
| "All threads eventually scheduled" | weak fairness | `\A t: WF_vars(Schedule(t))` |
| "No queue entry skipped forever" | strong fairness | `SF_vars(Dequeue)` |
| "Round-robin is fair" | weak fairness | `\A p: WF_vars(RunProcess(p))` |
| "Retry eventually succeeds if possible" | weak fairness | `WF_vars(Retry)` |

### Reachability

| Natural Language | Classification | TLA+ |
|-----------------|----------------|------|
| "Can always return to idle" | reachability | `Spec => <>[]Idle` |
| "Recovery state always reachable" | reachability | `[]<>CanRecover` |
| "Shutdown always possible" | reachability | `[]<>CanShutdown` |
| "Home screen reachable from any state" | reachability | `[](InApp => <>Home)` |
| "Transactions can always roll back" | reachability | `[](InTransaction => <>CanRollback)` |

### Mutual Exclusion

| Natural Language | Classification | TLA+ |
|-----------------|----------------|------|
| "At most one writer at a time" | mutex | `Cardinality(writers) <= 1` |
| "Critical section exclusive" | mutex | `Cardinality(in_critical) <= 1` |
| "Only one leader elected" | mutex | `Cardinality(leaders) <= 1` |
| "Resources locked exclusively" | mutex | `\A r: Cardinality(holders[r]) <= 1` |
| "No concurrent modifications" | mutex | `Cardinality(modifying) <= 1` |

## Borderline Cases

These cases require careful analysis:

### "Timeout" Requirements

"Request times out after 30 seconds"
- **If about single operation**: Dafny method timeout → infrastructure concern
- **If about observable behavior**: TLA+ temporal bound → `<>[30]Response \/ Timeout`
- **Resolution**: Usually TLA+ because it's about system behavior over time

### "Consistency" Requirements

"Data is consistent"
- **If about data shape**: Dafny Valid() predicate → `ghost predicate Valid() { Consistent(data) }`
- **If about eventual consistency**: TLA+ liveness → `[]<>Consistent`
- **Resolution**: Ask if it's point-in-time or eventually consistent

### "Atomicity" Requirements

"Transfer is atomic"
- **If about data integrity**: Dafny → `ensures (success ==> transferred) /\ (~success ==> unchanged)`
- **If about isolation**: TLA+ → mutual exclusion on transfer
- **Resolution**: Usually needs both models

### "Retry" Requirements

"Retry up to 3 times"
- **If about contract**: Dafny → parameter constraint `requires retries <= 3`
- **If about behavior**: TLA+ → state machine with retry counter
- **Resolution**: Usually TLA+ for the behavior pattern

## Composite Requirements

Some requirements decompose into multiple assertions:

### "Idempotent operations"

Decomposes to:
1. Dafny postcondition: `ensures result == old(result) if already_done`
2. TLA+ safety: repeated calls don't change state
3. Dafny invariant: operation can be detected as done

### "At-least-once delivery"

Decomposes to:
1. TLA+ liveness: `Sent ~> Delivered`
2. Dafny: receiver handles duplicates
3. TLA+ safety: message not lost

### "Exactly-once processing"

Decomposes to:
1. TLA+ liveness: eventually processed
2. TLA+ safety: not processed twice
3. Dafny: idempotency tracking structure
