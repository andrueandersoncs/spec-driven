# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

The **spec-driven** plugin enables specification-driven development using formal verification tools (Dafny + TLA+) to generate correct software from user intent. It extracts formal assertions from natural language requirements, verifies them using formal methods, and generates provably correct implementations.

## Dual Formal Model Architecture

The plugin uses two co-evolving formal models:

| Model | Focus | Tool | Purpose |
|-------|-------|------|---------|
| **Structure (Dafny)** | Single moment in time | Dafny verifier (Z3-backed) | Entity types, data constraints, method contracts |
| **Behavior (TLA+)** | Sequences of states | TLC model checker | State machines, temporal properties, concurrency |

**Key distinction**: Dafny models **space** (single state), TLA+ models **time** (state sequences).

## Assertion Classification Decision Tree

**Single moment in time?**
- YES → Dafny (Structure): data constraints, entity invariants, pre/postconditions
- NO → TLA+ (Behavior): liveness, safety, ordering, fairness properties

## Plugin Components

### Commands (`/commands`)
- `/probe-domain` - Bootstrap specification by identifying software archetype and domain
- `/interview` - Extract formal assertions from natural language requirements
- `/verify` - Run formal verification on specs (dafny verify, tlc)
- `/generate` - Generate implementation code from verified specifications
- `/reverse-engineer` - Extract specifications from existing codebase
- `/show-spec` - Display current specification state and assertion coverage
- `/resolve-conflict` - Resolve contradictions found during verification

### Agents (`/agents`)
- `assertion-generator` - Suggests candidate assertions from conversation
- `spec-validator` - Validates specs after changes
- `code-generator` - Generates TypeScript code from verified specs
- `conflict-resolver` - Explains and resolves verification failures

### Skills (`/skills`)
- `assertion-taxonomy` - Classification of assertions (Structure vs Behavior)
- `dafny-patterns` - Writing Dafny specifications
- `tla-patterns` - Writing TLA+ specifications
- `archetype-templates` - Default assertions by software type
- `domain-templates` - Domain-specific assertions
- `code-generation` - Code generation from specs

## Core Workflows

**Forward (Intent → Software):**
```
/probe-domain → /interview → /verify → /generate
```

**Reverse (Software → Intent):**
```
/reverse-engineer → /verify → /show-spec
```

## Project Structure (When Installed)

```
your-project/
├── specs/
│   ├── dafny/structure.dfy     # Structural specifications
│   ├── tla/behavior.tla        # Behavioral specifications
│   ├── tla/behavior.cfg        # TLC configuration
│   └── assertions.json         # Assertion manifest (single source of truth)
├── src/                        # Generated/implemented code
├── tests/                      # Generated tests
└── generated/                  # Dafny extraction output
```

## External Tool Requirements

- **Dafny**: `dafny verify` and `dafny build` commands
- **TLA+**: `tlc` (TLC model checker)
- **Nix** (optional): `nix develop` for reproducible environment

## Code Generation Modes

1. **Verified Extraction** - Dafny compiles to JavaScript, TypeScript wraps with type declarations
2. **Spec-Guided Generation** - LLM generates TypeScript constrained by specs with Zod schemas
3. **Contract-First** - Generate interfaces with TODO implementations

## Traceability Pattern

Every generated artifact must include source links:
```typescript
/**
 * @generated
 * @source-assertion A-047: "Account balance never negative"
 * @source-spec specs/dafny/structure.dfy:45-48
 * @verified 2024-01-15T10:30:00Z
 */
```

## Key Principles

1. **Always check `specs/assertions.json`** - Single source of truth for specification state
2. **Understand the dual-model approach** - Dafny handles structure, TLA+ handles behavior; they must stay in sync
3. **Use the taxonomy** - Classification determines whether to generate Dafny or TLA+
4. **Preserve traceability** - Every generated artifact should link back to source assertions
5. **Run verification loops** - Formal tools (Dafny, TLC) are ground truth; LLM reasoning must be verified
6. **Respect the workflow** - probe-domain → interview → verify → generate; skipping steps leads to incorrect code

## External References

- **Dafny Reference**: https://dafny.org/latest/DafnyRef/DafnyRef
- **TLA+ Repository**: https://github.com/tlaplus/tlaplus
- **TLA+ Examples**: https://github.com/tlaplus/Examples
- **Learn TLA+**: https://learntla.com/
