---
description: Start local development with spec-aware hot reloading
argument-hint: [port]
allowed-tools: Read, Bash, Glob, Write, AskUserQuestion
model: sonnet
---

# Development Server

Start a local development environment with spec-aware features.

## Prerequisites

Check project is ready:
- `package.json` exists with dev script
- `node_modules/` exists
- `src/index.ts` entry point exists

If not ready, instruct user to run `/scaffold` first.

## Archetype Detection

Read `specs/assertions.json` to determine archetype and appropriate dev mode:

| Archetype | Dev Mode |
|-----------|----------|
| CLI Tool | Interactive REPL |
| Web Service | HTTP server with hot reload |
| Library | Watch mode tests + example runner |
| Data Pipeline | Step-by-step execution with mock data |

## Start Development

### Web Service

```bash
bun run --watch src/index.ts
```

Report:
```
Development Server Started
==========================
  ➜ Local:   http://localhost:3000
  ➜ Network: http://192.168.x.x:3000

Features:
  • Hot reload on file changes
  • Effect Schema validation on all endpoints
  • Assertion tracking enabled

Press Ctrl+C to stop
```

If `$ARGUMENTS` contains a port number:
```bash
PORT=$ARGUMENTS bun run --watch src/index.ts
```

### CLI Tool

Create interactive REPL session:

```bash
bun repl
```

Or run with watch:
```bash
bun run --watch src/index.ts -- --help
```

Report:
```
CLI Development Mode
====================
Running: [project-name] CLI

Commands available:
  • [command1] - [description from spec]
  • [command2] - [description from spec]

File watching enabled - changes will restart automatically
```

### Library

```bash
bun test --watch
```

Report:
```
Library Development Mode
========================
Running tests in watch mode

Tests: 5 files, 23 tests
Coverage: 67% assertions

Changes to src/ or tests/ will re-run affected tests
```

### Data Pipeline

```bash
bun run src/index.ts --dry-run
```

Report:
```
Pipeline Development Mode
=========================
Running in dry-run mode with mock data

Steps:
  1. [step1] - simulated
  2. [step2] - simulated
  3. [step3] - simulated

Use --step N to run only step N
Use --real to use real data sources
```

## Spec-Aware Features

### Runtime Contract Checking

In development mode, wrap generated functions with runtime checks:

```typescript
// Development wrapper (auto-injected in dev mode)
function withContractCheck<T extends (...args: any[]) => any>(
  fn: T,
  assertionId: string
): T {
  return ((...args: Parameters<T>) => {
    const result = fn(...args);
    // Log assertion check
    console.log(`[${assertionId}] Contract checked`);
    return result;
  }) as T;
}
```

Report contract violations in console:
```
[A-001] ⚠️ Contract violation detected
  Function: withdraw
  Assertion: "Account balance never negative"
  State: balance = -50

  This should not happen if specs are correct.
  Run /verify to check formal proofs.
```

### Spec Change Detection

Watch `specs/` directory for changes:

```bash
# In a separate process or using Bun's watch
```

When spec changes detected:
```
Spec Change Detected
====================
Modified: specs/dafny/structure.dfy

Action needed:
  1. Run /verify to check consistency
  2. Run /generate to update implementation
  3. Restart dev server to pick up changes

Auto-restart? (y/n)
```

### Assertion Dashboard

For web services, add development endpoint:

`GET /_dev/assertions`

```json
{
  "assertions": [
    {
      "id": "A-001",
      "text": "Account balance never negative",
      "status": "verified",
      "lastChecked": "2024-01-15T10:30:00Z",
      "runtimeChecks": 145,
      "violations": 0
    }
  ],
  "coverage": {
    "tested": 2,
    "total": 3,
    "percentage": 67
  }
}
```

`GET /_dev/assertions/A-001`

Shows detailed assertion info including:
- Source spec location
- All code locations implementing this assertion
- Runtime check history

## Development Helpers

### Quick Commands

During dev session, remind user of available commands:

```
Dev Session Active
==================
Useful commands:
  /test          - Run tests with coverage
  /verify        - Check specs are still valid
  /generate      - Regenerate from specs
  /show-spec     - View current spec state

Keyboard shortcuts (in terminal):
  Ctrl+C         - Stop dev server
  r + Enter      - Force restart
```

### Error Linking

When runtime errors occur, link to source:

```
Runtime Error
=============
TypeError: Cannot read property 'balance' of undefined

Stack trace:
  at withdraw (src/domain/account.ts:45)
  at handler (src/api/account.ts:23)

Linked assertion: A-002
Source spec: specs/dafny/structure.dfy:15-17

Possible causes:
  • Account not found before withdraw
  • Missing null check in generated code

Recommendation:
  Add precondition: requires account != null
```

## Background Process Management

Dev server runs as a background process. Track with:

```
Dev Processes
=============
PID: 12345
  └─ bun run --watch src/index.ts
  └─ Started: 2024-01-15 10:30:00
  └─ Port: 3000
  └─ Status: running

Commands:
  /dev stop     - Stop dev server
  /dev restart  - Restart dev server
  /dev logs     - Show recent logs
```

## Integration with Workflow

The dev command fits into the full workflow:

```
/probe-domain → /interview → /verify → /generate → /scaffold → /test → /dev
                                                                         ↑
                                                              You are here!
```

While dev server is running:
- Edit specs → `/verify` → `/generate` → auto-restart
- Edit code manually → tests re-run → contract checks
- Add features → back to `/interview` to capture new assertions

## Stopping Development

When user wants to stop:

```
Stopping Development Server
===========================
Server stopped.

Session summary:
  • Runtime: 45 minutes
  • Requests handled: 234
  • Contract checks: 1,456
  • Violations: 0

Next steps:
  • /test --coverage  - Run final test coverage
  • /deploy          - Generate deployment artifacts
```
