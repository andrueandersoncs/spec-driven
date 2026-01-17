---
name: archetype-templates
description: This skill should be used when identifying software archetypes, loading default assertions for a project type, probing what kind of software is being built, or when the user asks "what type of software is this", "load CLI tool assertions", "load web service assertions", "what archetype is this", "initialize spec for library", "what assertions apply to my project type", "bootstrap assertions for a CLI", "default specs for an API", or describes building a specific type of application (CLI, library, web service, data pipeline, desktop app, compiler).
version: 0.1.0
---

# Archetype Templates

Load default assertions based on software archetype to bootstrap the specification process.

## Software Archetypes

Each archetype has common patterns that generate default assertion candidates.

| Archetype | Structure Focus | Behavior Focus |
|-----------|-----------------|----------------|
| CLI Tool | Arg schemas, exit codes, config | Command execution, I/O |
| Library/SDK | API types, compatibility | Error handling, stateless ops |
| Web Service | API contracts, data schemas | Request lifecycle, auth flows |
| Data Pipeline | Input/output schemas | Transform DAG, error recovery |
| Desktop App | UI state, document formats | User interactions, undo/redo |
| Compiler | AST, IR, target formats | Parse → Transform → Emit |

## Archetype Detection

Infer archetype from project context:

| Indicator | Suggested Archetype |
|-----------|---------------------|
| `package.json` with `bin` | CLI Tool |
| `main` entry with no `bin` | Library |
| Express/Fastify/Hono | Web Service |
| React/Vue/Svelte | Web App |
| Electron/Tauri | Desktop App |
| No UI, processes files | Data Pipeline |
| Parser/lexer/codegen files | Compiler |

After detection, confirm with user before loading assertions.

## CLI Tool Assertions

Default assertions for command-line tools.

### Structure (Dafny)

```
A-CLI-001: Exit code 0 indicates success
A-CLI-002: Exit code non-zero indicates error
A-CLI-003: Invalid arguments produce error exit
A-CLI-004: Help flag (-h, --help) shows usage
A-CLI-005: Version flag (-v, --version) shows version
A-CLI-006: Required arguments enforced
A-CLI-007: Config file schema validated
A-CLI-008: Output format matches specified type (JSON, text, etc.)
```

### Behavior (TLA+)

```
A-CLI-009: Stdout for normal output, stderr for errors
A-CLI-010: Ctrl+C produces graceful shutdown
A-CLI-011: Progress indication for long operations
A-CLI-012: Partial failure doesn't corrupt output
```

## Library/SDK Assertions

Default assertions for reusable code packages.

### Structure (Dafny)

```
A-LIB-001: Public API types are documented
A-LIB-002: No side effects without explicit opt-in
A-LIB-003: Errors returned, not thrown (or documented)
A-LIB-004: Input validation at public boundaries
A-LIB-005: Null/undefined handling explicit
A-LIB-006: Generic types properly constrained
```

### Behavior (TLA+)

```
A-LIB-007: Stateless functions are pure
A-LIB-008: Resource cleanup on scope exit
A-LIB-009: Async operations cancellable
A-LIB-010: Concurrent access safe (if applicable)
```

## Web Service Assertions

Default assertions for HTTP APIs.

### Structure (Dafny)

```
A-WEB-001: Request body schema enforced
A-WEB-002: Response body matches documented schema
A-WEB-003: Authentication required for protected routes
A-WEB-004: Input sanitized before use
A-WEB-005: Error responses have consistent format
A-WEB-006: 2xx for success, 4xx for client error, 5xx for server error
```

### Behavior (TLA+)

```
A-WEB-007: Unauthenticated requests rejected (401/403)
A-WEB-008: Invalid input returns 4xx, not 5xx
A-WEB-009: Health endpoint always responds
A-WEB-010: Requests have timeout
A-WEB-011: Rate limiting prevents abuse
A-WEB-012: Idempotent endpoints handle retry
```

## Data Pipeline Assertions

Default assertions for batch/stream processing.

### Structure (Dafny)

```
A-PIPE-001: Input schema validated at boundary
A-PIPE-002: Output schema matches contract
A-PIPE-003: Transform preserves required fields
A-PIPE-004: Null handling explicit at each stage
A-PIPE-005: Schema evolution handled
```

### Behavior (TLA+)

```
A-PIPE-006: Failed records don't block pipeline
A-PIPE-007: Exactly-once or at-least-once semantics declared
A-PIPE-008: Backpressure prevents memory exhaustion
A-PIPE-009: Checkpoint enables restart
A-PIPE-010: Dead letter queue for unprocessable records
```

## Desktop App Assertions

Default assertions for GUI applications.

### Structure (Dafny)

```
A-DESK-001: Document format versioned
A-DESK-002: Preferences schema defined
A-DESK-003: UI state serializable
A-DESK-004: File operations validate paths
```

### Behavior (TLA+)

```
A-DESK-005: Undo/redo stack maintained
A-DESK-006: Autosave prevents data loss
A-DESK-007: Long operations don't freeze UI
A-DESK-008: Dirty state tracked for unsaved changes
A-DESK-009: Graceful degradation on missing resources
```

## Compiler/Interpreter Assertions

Default assertions for language tools.

### Structure (Dafny)

```
A-COMP-001: AST nodes well-typed
A-COMP-002: IR preserves semantics
A-COMP-003: Source locations tracked through transforms
A-COMP-004: Symbol tables consistent
```

### Behavior (TLA+)

```
A-COMP-005: Parse → Check → Transform → Emit pipeline
A-COMP-006: Errors don't abort entire compilation
A-COMP-007: Error recovery produces useful diagnostics
A-COMP-008: Incremental compilation sound
```

## Using Templates

### Loading Process

1. Detect or ask for archetype
2. Load archetype's default assertions
3. Present to user for confirmation/modification
4. User confirms, denies, or refines each assertion
5. Confirmed assertions become specification seed

### Assertion Status

```json
{
  "id": "A-CLI-001",
  "natural": "Exit code 0 indicates success",
  "status": "pending",  // pending | confirmed | denied | refined
  "refinement": null,   // user's modified version
  "source": "archetype-cli"
}
```

### Customization

Templates are starting points. Expect users to:
- **Confirm** common cases unchanged
- **Deny** inapplicable assertions
- **Refine** assertions that need domain specifics
- **Add** domain-specific assertions not in template

## Additional Resources

### Example Files
- **`examples/cli-tool-assertions.json`** - Complete CLI tool assertion set in JSON format
- **`examples/web-service-assertions.json`** - Complete web service assertion set in JSON format

### Related Skills
- `domain-templates` - Domain-specific overlays (finance, auth, etc.)
- `assertion-taxonomy` - How to classify custom assertions
