# Effect Schema Reference Guide

> **Source**: This reference consolidates information from the [Effect Schema Documentation](https://effect.website/docs/schema/introduction) and [Effect Documentation](https://effect.website/docs).

## Overview

Effect Schema provides a blueprint for describing the structure and data types of your data. It enables validation, transformation, and assertion operations across TypeScript applications.

## Schema Type Structure

```typescript
Schema<Type, Encoded, Requirements>
```

| Parameter | Description |
|-----------|-------------|
| **Type** | The decoded output value (what your code works with) |
| **Encoded** | The input/encoded format (defaults to Type) |
| **Requirements** | Contextual dependencies needed for execution |

## Core Principle: Decoding and Encoding

- **Decoding**: Transforms external data into your application's internal types—critical for untrusted sources (APIs, user input)
- **Encoding**: Converts internal types back to formats expected by external systems

> The fundamental principle: "encode + decode should return the original value."
>
> *Source: [Effect Schema Introduction](https://effect.website/docs/schema/introduction)*

## TypeScript Configuration

Enable these options in `tsconfig.json`:

```json
{
  "compilerOptions": {
    "strict": true,
    "exactOptionalPropertyTypes": true
  }
}
```

`exactOptionalPropertyTypes` provides stronger type safety for optional properties.

## Primitive Schemas

```typescript
import { Schema } from 'effect';

// Built-in primitives
Schema.String
Schema.Number
Schema.Boolean
Schema.BigIntFromSelf
Schema.SymbolFromSelf
Schema.Date
Schema.Undefined
Schema.Null
Schema.Never
Schema.Unknown
Schema.Any
Schema.Void
```

## Literal and Union Schemas

### Literals

```typescript
// Single literal
const Active = Schema.Literal("active");

// Union of literals (creates a discriminated union)
const Status = Schema.Literal("pending", "active", "completed");
type Status = typeof Status.Type; // "pending" | "active" | "completed"
```

### Unions

```typescript
// Combine multiple schemas
const StringOrNumber = Schema.Union(Schema.String, Schema.Number);

// Important: union members are evaluated in order
// Place more specific schemas before general ones
const Specific = Schema.Union(
  Schema.Literal("special"),  // Check specific first
  Schema.String               // Then general
);
```

> "When decoding, union members are evaluated in the order they are defined," so placing more specific schemas before general ones prevents data loss.
>
> *Source: [Effect Schema Basic Usage](https://effect.website/docs/schema/basic-usage)*

## Struct Schemas

```typescript
const Person = Schema.Struct({
  name: Schema.String,
  age: Schema.Number,
  email: Schema.optional(Schema.String)
});

type Person = typeof Person.Type;
// { name: string; age: number; email?: string }
```

## Array and Tuple Schemas

```typescript
// Arrays (variable length)
const Numbers = Schema.Array(Schema.Number);

// Tuples (fixed length)
const Point = Schema.Tuple(Schema.Number, Schema.Number);

// Tuple with rest elements
const AtLeastOne = Schema.Tuple(
  [Schema.String],           // Required first element
  Schema.String              // Rest elements
);
```

## Refinements and Filters

### Built-in Refinements

```typescript
// Number refinements
Schema.Number.pipe(
  Schema.int(),                    // Integer
  Schema.positive(),               // > 0
  Schema.nonNegative(),            // >= 0
  Schema.negative(),               // < 0
  Schema.nonPositive(),            // <= 0
  Schema.greaterThan(5),           // > 5
  Schema.greaterThanOrEqualTo(5),  // >= 5
  Schema.lessThan(10),             // < 10
  Schema.lessThanOrEqualTo(10),    // <= 10
  Schema.between(1, 10)            // 1 <= x <= 10
);

// String refinements
Schema.String.pipe(
  Schema.minLength(1),             // Length >= 1
  Schema.maxLength(100),           // Length <= 100
  Schema.length(5),                // Exact length
  Schema.nonEmpty(),               // Length > 0
  Schema.pattern(/^[a-z]+$/),      // Regex match
  Schema.startsWith("prefix"),
  Schema.endsWith("suffix"),
  Schema.includes("substring"),
  Schema.trimmed()                 // No leading/trailing whitespace
);
```

### Custom Filters

```typescript
// Simple filter
const Even = Schema.Number.pipe(
  Schema.filter((n) => n % 2 === 0)
);

// Filter with custom message
const PositiveEven = Schema.Number.pipe(
  Schema.filter(
    (n) => n > 0 && n % 2 === 0,
    { message: () => "Expected a positive even number" }
  )
);

// Struct-level filter (validates relationships)
const ValidRange = Schema.Struct({
  min: Schema.Number,
  max: Schema.Number
}).pipe(
  Schema.filter(
    (data) => data.min <= data.max
      ? true
      : "min must be less than or equal to max"
  )
);
```

## Branded Types

Branded types provide compile-time distinction between structurally identical types:

```typescript
// Define branded type
const UserId = Schema.String.pipe(
  Schema.minLength(1),
  Schema.brand("UserId")
);
type UserId = typeof UserId.Type;

const OrderId = Schema.String.pipe(
  Schema.minLength(1),
  Schema.brand("OrderId")
);
type OrderId = typeof OrderId.Type;

// Compile-time safety: can't mix UserIds and OrderIds
function getUser(id: UserId): User { /* ... */ }
function getOrder(id: OrderId): Order { /* ... */ }

const userId = Schema.decodeUnknownSync(UserId)("user-123");
const orderId = Schema.decodeUnknownSync(OrderId)("order-456");

getUser(userId);   // OK
getUser(orderId);  // Compile error!
```

> See [Branded Types](https://effect.website/docs/schema/advanced-usage#branded-types) for advanced patterns.

## Decoding and Encoding Operations

### Synchronous Decoding

```typescript
import { Schema } from 'effect';

const Person = Schema.Struct({
  name: Schema.String,
  age: Schema.Number
});

// Throws on failure
const person = Schema.decodeUnknownSync(Person)({
  name: "Alice",
  age: 30
});

// Returns Either
const result = Schema.decodeUnknownEither(Person)(input);
if (result._tag === "Right") {
  console.log(result.right); // Decoded value
} else {
  console.log(result.left);  // ParseError
}
```

### Effect-based Decoding

```typescript
import { Schema, Effect } from 'effect';

// Returns Effect<A, ParseError>
const decode = Schema.decodeUnknown(Person);
const program = decode(input).pipe(
  Effect.map((person) => person.name)
);
```

### Encoding

```typescript
// Encode validated data back to external format
const encoded = Schema.encodeSync(Person)({
  name: "Alice",
  age: 30
});
```

## Error Messages

### Default Messages

Effect automatically generates informative error messages:

```
Expected string, actual null
Expected { name: string; age: number }, actual {}
```

### Identifier Annotation

Use `identifier` to simplify error messages:

```typescript
const Name = Schema.String.pipe(
  Schema.minLength(1)
).annotations({ identifier: "Name" });

// Error: "Expected Name, actual null" (cleaner than full type)
```

### Custom Messages

```typescript
const Password = Schema.String.pipe(
  Schema.minLength(8)
).annotations({
  message: () => "Password must be at least 8 characters"
});

// With override to replace all nested messages
const Form = Schema.Struct({
  password: Password
}).annotations({
  message: () => ({
    message: "Invalid form submission",
    override: true  // Suppresses nested error messages
  })
});
```

> Setting `override: true` makes your message replace all inner messages, useful for creating comprehensive validation descriptions.
>
> *Source: [Effect Schema Error Messages](https://effect.website/docs/schema/error-messages)*

## Mapping from Dafny to Effect Schema

| Dafny Construct | Effect Schema Equivalent |
|-----------------|-------------------------|
| `type X = x: int \| x > 0` | `Schema.Number.pipe(Schema.int(), Schema.positive())` |
| `type X = x: int \| x >= 0` | `Schema.Number.pipe(Schema.int(), Schema.nonNegative())` |
| `type X = x: int \| a <= x <= b` | `Schema.Number.pipe(Schema.int(), Schema.between(a, b))` |
| `type X = s: string \| \|s\| > 0` | `Schema.String.pipe(Schema.nonEmpty())` |
| `type X = s: string \| \|s\| <= n` | `Schema.String.pipe(Schema.maxLength(n))` |
| `datatype X = A \| B \| C` | `Schema.Literal("A", "B", "C")` |
| `class C { var x: int; var y: string }` | `Schema.Struct({ x: Schema.Int, y: Schema.String })` |
| Class `Valid()` predicate | `Schema.Struct({...}).pipe(Schema.filter(...))` |

## Example: From Dafny to Effect Schema

### Dafny Specification

```dafny
type Age = x: int | 0 < x < 150
type NonEmptyString = s: string | |s| > 0

class Account {
  var id: string
  var balance: int
  var owner: NonEmptyString

  ghost predicate Valid() {
    balance >= 0 && |id| > 0
  }
}
```

### Generated Effect Schema

```typescript
import { Schema } from 'effect';

// Refinement types
export const Age = Schema.Number.pipe(
  Schema.int(),
  Schema.greaterThan(0),
  Schema.lessThan(150),
  Schema.brand("Age")
);
export type Age = typeof Age.Type;

export const NonEmptyString = Schema.String.pipe(
  Schema.minLength(1),
  Schema.brand("NonEmptyString")
);
export type NonEmptyString = typeof NonEmptyString.Type;

// Class with invariant
export const Account = Schema.Struct({
  id: Schema.String.pipe(Schema.minLength(1)),
  balance: Schema.Number.pipe(Schema.int(), Schema.nonNegative()),
  owner: NonEmptyString
}).annotations({ identifier: "Account" });
export type Account = typeof Account.Type;
```

## Best Practices

### 1. Define Schemas at Module Level

```typescript
// Good: reusable, consistent
export const UserSchema = Schema.Struct({...});

// Avoid: inline schemas lose reusability
function process(data: unknown) {
  return Schema.decodeUnknownSync(Schema.Struct({...}))(data);
}
```

### 2. Use Branded Types for Domain Concepts

```typescript
// Better than plain strings
const Email = Schema.String.pipe(
  Schema.pattern(/^[^@]+@[^@]+$/),
  Schema.brand("Email")
);
```

### 3. Validate at Boundaries, Trust Internally

```typescript
// Validate at API boundary
app.post('/users', async (c) => {
  const input = Schema.decodeUnknownSync(CreateUserSchema)(await c.req.json());
  // Inside: types are trusted
  return createUser(input);
});
```

### 4. Use Identifiers for Better Errors

```typescript
const User = Schema.Struct({...}).annotations({
  identifier: "User"
});
```

## External References

- [Effect Schema Introduction](https://effect.website/docs/schema/introduction)
- [Effect Schema Basic Usage](https://effect.website/docs/schema/basic-usage)
- [Effect Schema Filters](https://effect.website/docs/schema/filters)
- [Effect Schema Branded Types](https://effect.website/docs/schema/advanced-usage#branded-types)
- [Effect Schema Error Messages](https://effect.website/docs/schema/error-messages)
- [Effect Documentation](https://effect.website/docs)
- [Effect GitHub](https://github.com/Effect-TS/effect)
