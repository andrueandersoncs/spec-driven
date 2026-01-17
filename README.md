# spec-driven

A Claude Code plugin for specification-driven development using formal verification.

## Overview

This plugin enables Claude Code to act as a **specification-driven development agent** that:

1. **Extracts formal assertions** from natural language requirements
2. **Builds dual formal models**: Dafny (structure) + TLA+ (behavior)
3. **Verifies specifications** using `dafny verify` and TLC model checker
4. **Generates correct software** from verified specifications
5. **Reverse-engineers intent** from existing codebases

## Installation

### Prerequisites

The plugin requires Dafny and TLA+ tools. The easiest way to get them is with Nix:

```bash
# Copy the flake.nix template to your project
cp /path/to/plugin/templates/flake.nix ./flake.nix

# Enter the development shell
nix develop
```

Or install manually:
- **Dafny**: https://github.com/dafny-lang/dafny/releases (see [Dafny Reference Manual](https://dafny.org/latest/DafnyRef/DafnyRef))
- **TLA+ Tools**: https://github.com/tlaplus/tlaplus/releases (see [TLA+ Resources](#tla-resources) below)

### Plugin Installation

```bash
# Install from plugin directory
claude --plugin-dir /path/to/spec-driven
```

## Commands

| Command | Description |
|---------|-------------|
| `/probe-domain` | Bootstrap specification by identifying software archetype and domain |
| `/interview` | Extract formal assertions from natural language requirements |
| `/verify` | Run formal verification on Dafny and TLA+ specs |
| `/generate` | Generate implementation code from verified specifications |
| `/reverse-engineer` | Extract specifications from existing codebase |
| `/show-spec` | Display current specification state and assertion coverage |
| `/resolve-conflict` | Resolve contradictions found during verification |

## Workflow

### Forward: Intent → Software

```
1. /probe-domain     - Identify what you're building
2. /interview        - Extract assertions from requirements
3. /verify           - Check specifications for consistency
4. /generate         - Create implementation code
```

### Reverse: Software → Intent

```
1. /reverse-engineer - Extract specs from existing code
2. /verify           - Check extracted specs
3. /show-spec        - Review and confirm
```

## Project Structure

When using this plugin, your project will have:

```
your-project/
├── specs/
│   ├── dafny/
│   │   └── structure.dfy    # Structural specs (types, contracts)
│   ├── tla/
│   │   ├── behavior.tla     # Behavioral specs (state machines)
│   │   └── behavior.cfg     # TLC configuration
│   └── assertions.json      # Assertion manifest
├── src/                     # Generated/implemented code
├── tests/                   # Generated tests
└── flake.nix               # Nix development environment
```

## Skills

The plugin provides specialized knowledge for:

- **assertion-taxonomy**: Classification of assertions (structure vs behavior)
- **dafny-patterns**: Writing Dafny specifications
- **tla-patterns**: Writing TLA+ specifications
- **archetype-templates**: Default assertions by software type
- **domain-templates**: Domain-specific assertions (finance, auth, etc.)
- **code-generation**: Generating TypeScript from specs

## Agents

The plugin includes proactive agents:

- **assertion-generator**: Suggests assertions from conversation
- **spec-validator**: Validates specs after changes
- **conflict-resolver**: Explains and resolves verification failures
- **code-generator**: Generates code from verified specs

## Assertion Types

### Structure (Dafny)

| Type | Example |
|------|---------|
| Data constraint | "Age must be positive" |
| Invariant | "Balance never negative" |
| Precondition | "Can withdraw only if sufficient funds" |
| Postcondition | "Deposit increases balance by exact amount" |

### Behavior (TLA+)

| Type | Example |
|------|---------|
| Safety | "Never process payment twice" |
| Liveness | "Every request eventually gets response" |
| Ordering | "Auth must happen before API call" |
| Fairness | "No request starves indefinitely" |

## Example Session

```
You: I want to build a banking API where users can deposit and withdraw money

Claude: I'll use /probe-domain to set up your project...
        Detected: Web Service archetype, Finance domain
        Loaded 20 seed assertions

You: Users shouldn't be able to withdraw more than their balance

Claude: [assertion-generator agent activates]
        I've identified these assertions:
        - A-001: "Balance must be non-negative" (invariant)
        - A-002: "Withdraw requires amount <= balance" (precondition)
        - A-003: "Successful withdraw decreases balance by exact amount" (postcondition)

You: Confirm all

Claude: Added to specs/assertions.json. Running /verify...
        ✓ Dafny verification passed
        ✓ Specifications are consistent

You: Generate the code

Claude: [code-generator agent activates]
        Generated:
        - src/types/account.ts (Effect Schemas)
        - src/validation/account.ts (validators)
        - src/domain/account.ts (business logic)
        - tests/account.test.ts (property tests)
```

## Configuration

Create `.claude/spec-driven.local.md` for project-specific settings:

```yaml
---
archetype: web-service
domains:
  - finance
  - auth
preferences:
  autoVerify: true
  generateTests: true
  targetLanguage: typescript
---

# Project-specific notes and context
```

## TLA+ Resources

Essential resources for writing and understanding TLA+ specifications:

| Resource | Description |
|----------|-------------|
| [TLA+ Repository](https://github.com/tlaplus/tlaplus) | Official TLA+ tools (TLC model checker, SANY parser, PlusCal translator) |
| [TLA+ Examples](https://github.com/tlaplus/Examples) | Curated collection of TLA+ specifications including Paxos, Two-Phase Commit, and more |
| [TLA+ Cheatsheet](https://lamport.azurewebsites.net/tla/summary-standalone.pdf) | Quick reference for TLA+ operators and syntax |
| [Learn TLA+](https://learntla.com/) | Interactive tutorial for learning TLA+ |
| [TLA+ Home](https://lamport.azurewebsites.net/tla/tla.html) | Official TLA+ website with video course and documentation |

## Dafny Resources

Essential resources for writing and understanding Dafny specifications:

| Resource | Description |
|----------|-------------|
| [Dafny Repository](https://github.com/dafny-lang/dafny) | Official Dafny verification language |
| [Dafny Reference Manual](https://dafny.org/latest/DafnyRef/DafnyRef) | Complete language reference |
| [Dafny Tutorial](https://dafny.org/latest/OnlineTutorial/guide) | Getting started guide |

## Effect Resources

This plugin uses [Effect](https://effect.website/) for TypeScript runtime validation and error handling:

| Resource | Description |
|----------|-------------|
| [Effect Documentation](https://effect.website/docs) | Official Effect documentation |
| [Effect Schema](https://effect.website/docs/schema/introduction) | Schema validation (replaces Zod) |
| [Effect GitHub](https://github.com/Effect-TS/effect) | Effect source code repository |
| [Effect Examples](https://github.com/Effect-TS/examples) | Example projects using Effect |
| [Effect LSP/DevTools](https://effect.website/docs/getting-started/devtools/) | IDE integration and developer tools |

## License

MIT
