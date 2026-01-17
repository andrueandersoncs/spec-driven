# Effect Patterns Reference

Comprehensive reference for Effect library patterns used in spec-driven TypeScript applications.

> **Source**: [Effect Documentation](https://effect.website/docs)

## Table of Contents

- [Schema Filters](#schema-filters)
- [Branded Types](#branded-types)
- [Error Handling with TaggedError](#error-handling-with-taggederror)
- [Effect.gen Pattern](#effectgen-pattern)
- [Dafny to Effect Schema Mapping](#dafny-to-effect-schema-mapping)

---

## Schema Filters

Effect Schema provides built-in filters for common validation patterns.

### Number Filters

```typescript
import { Schema } from "effect"

// Basic constraints
Schema.Number.pipe(Schema.greaterThan(0))           // x > 0
Schema.Number.pipe(Schema.lessThan(100))            // x < 100
Schema.Number.pipe(Schema.greaterThanOrEqualTo(0))  // x >= 0
Schema.Number.pipe(Schema.lessThanOrEqualTo(100))   // x <= 100

// Range (inclusive)
Schema.Number.pipe(Schema.between(0, 100))          // 0 <= x <= 100

// Integer validation
Schema.Number.pipe(Schema.int())                    // Must be integer
Schema.Int                                          // Shorthand

// Sign constraints
Schema.Number.pipe(Schema.positive())               // x > 0
Schema.Number.pipe(Schema.nonNegative())            // x >= 0
Schema.Number.pipe(Schema.negative())               // x < 0
Schema.Number.pipe(Schema.nonPositive())            // x <= 0

// Special values
Schema.Number.pipe(Schema.nonNaN())                 // Not NaN
Schema.Number.pipe(Schema.finite())                 // Not Infinity

// Multiple
Schema.Number.pipe(Schema.multipleOf(5))            // x % 5 === 0

// Pre-defined types
Schema.Uint8                                        // 0-255 unsigned integer
```

### String Filters

```typescript
import { Schema } from "effect"

// Length constraints
Schema.String.pipe(Schema.minLength(1))             // |s| >= 1
Schema.String.pipe(Schema.maxLength(100))           // |s| <= 100
Schema.String.pipe(Schema.length(10))               // |s| === 10
Schema.String.pipe(Schema.length({ min: 2, max: 4 })) // 2 <= |s| <= 4

// Non-empty shorthand
Schema.String.pipe(Schema.nonEmptyString())
Schema.NonEmptyString                               // Shorthand

// Pattern matching
Schema.String.pipe(Schema.pattern(/^[a-z]+$/))      // Regex match
Schema.String.pipe(Schema.startsWith("prefix"))     // Starts with
Schema.String.pipe(Schema.endsWith("suffix"))       // Ends with
Schema.String.pipe(Schema.includes("substring"))    // Contains

// Whitespace and case
Schema.String.pipe(Schema.trimmed())                // No leading/trailing whitespace
Schema.String.pipe(Schema.lowercased())             // All lowercase
Schema.String.pipe(Schema.uppercased())             // All uppercase
Schema.String.pipe(Schema.capitalized())            // First letter uppercase
```

### Custom Filters

```typescript
import { Schema } from "effect"

// Simple predicate filter
const LongString = Schema.String.pipe(
  Schema.filter(
    (s) => s.length >= 10 || "a string at least 10 characters long"
  )
)

// Filter with path for structured errors
const MyForm = Schema.Struct({
  password: Schema.String.pipe(Schema.minLength(2)),
  confirm_password: Schema.String.pipe(Schema.minLength(2))
}).pipe(
  Schema.filter((input) => {
    if (input.password !== input.confirm_password) {
      return {
        path: ["confirm_password"],
        message: "Passwords do not match"
      }
    }
  })
)
```

---

## Branded Types

Branded types provide compile-time distinction between structurally identical types.

### Schema-Based Branding

```typescript
import { Schema } from "effect"

// Define branded type with validation
const PositiveInt = Schema.Number.pipe(
  Schema.int(),
  Schema.positive(),
  Schema.brand("PositiveInt")
)
type PositiveInt = Schema.Schema.Type<typeof PositiveInt>

const AccountId = Schema.String.pipe(
  Schema.minLength(1),
  Schema.brand("AccountId")
)
type AccountId = Schema.Schema.Type<typeof AccountId>

// Parse to create branded values
const accountId = Schema.decodeUnknownSync(AccountId)("acc-123")
const amount = Schema.decodeUnknownSync(PositiveInt)(100)

// Type safety - compiler prevents mixing
function withdraw(id: AccountId, amount: PositiveInt): void {
  // amount is guaranteed positive at compile time
}
```

### Brand Module (Runtime Branding)

```typescript
import { Brand } from "effect"

// Define refined branded type
type Int = number & Brand.Brand<"Int">

const Int = Brand.refined<Int>(
  (n) => Number.isInteger(n),
  (n) => Brand.error(`Expected ${n} to be an integer`)
)

type Positive = number & Brand.Brand<"Positive">

const Positive = Brand.refined<Positive>(
  (n) => n > 0,
  (n) => Brand.error(`Expected ${n} to be positive`)
)

// Combine branded types
const PositiveInt = Brand.all(Int, Positive)
type PositiveInt = Brand.Brand.FromConstructor<typeof PositiveInt>

// Usage
const good: PositiveInt = PositiveInt(10)    // OK
const bad1: PositiveInt = PositiveInt(-5)    // throws
const bad2: PositiveInt = PositiveInt(3.14)  // throws
```

---

## Error Handling with TaggedError

TaggedError provides discriminated union errors for precise error handling.

### Defining Tagged Errors

```typescript
import { Data } from "effect"

// Error with _tag: "HttpError"
class HttpError extends Data.TaggedError("HttpError")<{}> {}

// Error with payload
class ValidationError extends Data.TaggedError("ValidationError")<{
  readonly field: string
  readonly message: string
}> {}

// Error with computed properties
class NotFound extends Data.TaggedError("NotFound")<{
  readonly resource: string
  readonly id: string
}> {
  get message() {
    return `${this.resource} with id ${this.id} not found`
  }
}
```

### Handling Tagged Errors

```typescript
import { Effect, Data, Random } from "effect"

class FooError extends Data.TaggedError("Foo")<{ message: string }> {}
class BarError extends Data.TaggedError("Bar")<{ code: number }> {}

const program = Effect.gen(function* () {
  const n = yield* Random.next
  if (n < 0.3) return yield* new FooError({ message: "Oh no!" })
  if (n < 0.6) return yield* new BarError({ code: 500 })
  return "success"
})

// Handle single tag
const recovered1 = program.pipe(
  Effect.catchTag("Foo", (e) => Effect.succeed(`Caught Foo: ${e.message}`))
)

// Handle multiple tags
const recovered2 = program.pipe(
  Effect.catchTags({
    Foo: (e) => Effect.succeed(`Foo error: ${e.message}`),
    Bar: (e) => Effect.succeed(`Bar error: ${e.code}`)
  })
)
```

---

## Effect.gen Pattern

The generator pattern for sequential effectful operations.

### Basic Usage

```typescript
import { Effect } from "effect"

const program = Effect.gen(function* () {
  const a = yield* Effect.succeed(1)
  const b = yield* Effect.succeed(2)
  return a + b
})

// Run the program
Effect.runPromise(program).then(console.log) // 3
```

### With Error Handling

```typescript
import { Effect, Data } from "effect"

class InsufficientFunds extends Data.TaggedError("InsufficientFunds")<{
  balance: number
  requested: number
}> {}

const withdraw = (
  account: { balance: number },
  amount: number
): Effect.Effect<{ balance: number }, InsufficientFunds> =>
  Effect.gen(function* () {
    if (amount > account.balance) {
      return yield* Effect.fail(
        new InsufficientFunds({
          balance: account.balance,
          requested: amount
        })
      )
    }
    return { balance: account.balance - amount }
  })
```

### Combining Effects

```typescript
import { Effect } from "effect"

const fetchUser = (id: string) => Effect.succeed({ id, name: "Alice" })
const fetchPosts = (userId: string) => Effect.succeed([{ title: "Hello" }])

const program = Effect.gen(function* () {
  const user = yield* fetchUser("123")
  const posts = yield* fetchPosts(user.id)
  return { user, posts }
})
```

---

## Dafny to Effect Schema Mapping

Complete mapping from Dafny refinement types to Effect Schema.

### Numeric Types

| Dafny | Effect Schema |
|-------|---------------|
| `type X = x: int \| x > 0` | `Schema.Number.pipe(Schema.int(), Schema.positive())` |
| `type X = x: int \| x >= 0` | `Schema.Number.pipe(Schema.int(), Schema.nonNegative())` |
| `type X = x: int \| x < 0` | `Schema.Number.pipe(Schema.int(), Schema.negative())` |
| `type X = x: int \| a <= x <= b` | `Schema.Number.pipe(Schema.int(), Schema.between(a, b))` |
| `type X = x: real \| x >= 0` | `Schema.Number.pipe(Schema.nonNegative())` |

### String Types

| Dafny | Effect Schema |
|-------|---------------|
| `type X = s: string \| \|s\| > 0` | `Schema.String.pipe(Schema.minLength(1))` or `Schema.NonEmptyString` |
| `type X = s: string \| \|s\| <= n` | `Schema.String.pipe(Schema.maxLength(n))` |
| `type X = s: string \| a <= \|s\| <= b` | `Schema.String.pipe(Schema.length({ min: a, max: b }))` |

### Algebraic Types

| Dafny | Effect Schema |
|-------|---------------|
| `datatype X = A \| B \| C` | `Schema.Literal("A", "B", "C")` |
| `class C { var x: int; var y: string }` | `Schema.Struct({ x: Schema.Int, y: Schema.String })` |

### Class Invariants

```dafny
// Dafny
class Account {
  var balance: int
  var limit: int
  ghost predicate Valid() {
    balance >= -limit && limit >= 0
  }
}
```

```typescript
// Effect Schema
const AccountSchema = Schema.Struct({
  balance: Schema.Int,
  limit: Schema.Number.pipe(Schema.int(), Schema.nonNegative())
}).pipe(
  Schema.filter((data) =>
    data.balance >= -data.limit
      ? true
      : "Balance cannot exceed overdraft limit"
  )
)
```

---

## External References

- [Effect Schema Documentation](https://effect.website/docs/schema/introduction)
- [Effect Schema Filters](https://effect.website/docs/schema/filters)
- [Effect Error Management](https://effect.website/docs/error-management/expected-errors)
- [Effect Branded Types](https://effect.website/docs/code-style/branded-types)
- [Effect Data Types](https://effect.website/docs/data-types/data)
- [Effect Platform HTTP](https://effect.website/docs/platform/http-server)
