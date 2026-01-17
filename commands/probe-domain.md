---
description: Bootstrap specification by identifying software archetype and domain
allowed-tools: Read, Write, Glob, Grep, AskUserQuestion
model: sonnet
---

# Domain Probing

Begin the specification-driven development process by establishing context about what is being built.

## Phase 1: Project Analysis

First, analyze the existing project structure (if any) to infer archetype:

Check for project indicators:
- package.json with `bin` field → likely CLI tool
- package.json with Express/Fastify/Hono → likely Web Service
- package.json as library (no bin, no server) → likely Library
- React/Vue/Svelte presence → likely Web App
- No package.json but processing scripts → likely Data Pipeline
- Parser/lexer/codegen files → likely Compiler

If project structure exists, propose detected archetype.
If greenfield (no existing code), proceed to ask.

## Phase 2: Archetype Identification

Present archetype options using AskUserQuestion:

**Question**: "What type of software are you building?"
**Options**:
- CLI Tool - Command-line application with args, flags, exit codes
- Library/SDK - Reusable code package with public API
- Web Service - HTTP API (REST, GraphQL, etc.)
- Web App - Browser-based application with UI
- Data Pipeline - Batch or stream data processing
- Desktop App - Native GUI application
- Compiler/Interpreter - Language processing tool
- Other - I'll describe it

## Phase 3: Domain Identification

Based on archetype, ask about applicable domains:

**Question**: "What domain(s) does this operate in? (Select all that apply)"
**Options** (varies by archetype):
- Finance/Banking - Monetary transactions, accounting
- Healthcare - Patient data, HIPAA compliance
- Auth/Identity - Authentication, authorization, sessions
- Multi-tenant - Shared infrastructure, tenant isolation
- E-commerce - Products, orders, inventory
- Real-time - Low-latency, streaming data
- None specific - General purpose application

## Phase 4: Actor Enumeration

**Question**: "Who or what interacts with this system?"
Examples to prompt:
- Human users (roles: admin, customer, etc.)
- External APIs or services
- Background jobs or schedulers
- Other systems via integration

Collect actor list for capability mapping.

## Phase 5: Capability Mapping

For each actor identified, ask:
**Question**: "What can [actor] do?"
Present common capabilities:
- Create/Read/Update/Delete operations
- Special actions (login, export, approve, etc.)
- Query or search operations

Build actor × capability matrix.

## Phase 6: Boundary Identification

**Question**: "Where does your system end?"
Identify:
- External dependencies (databases, APIs, services)
- Trust boundaries (what's trusted vs untrusted)
- Data sources and sinks

## Phase 7: Negative Space

**Question**: "What is this system explicitly NOT?"
Examples:
- "Not multi-tenant"
- "Not real-time"
- "Not distributed"
- "Not handling payments directly"

These constraints prevent over-engineering.

## Output

After completing probing, create the specification directory structure:

```
specs/
├── dafny/
│   └── .gitkeep
├── tla/
│   └── .gitkeep
└── assertions.json
```

Initialize `specs/assertions.json` with:
```json
{
  "version": "1.0.0",
  "archetype": "[detected archetype]",
  "domains": ["[detected domains]"],
  "actors": ["[enumerated actors]"],
  "boundaries": ["[identified boundaries]"],
  "constraints": ["[negative constraints]"],
  "assertions": []
}
```

Load archetype and domain assertion templates using the archetype-templates and domain-templates skills.

Present the seed assertions to user for review, marking them as "pending" status.

Conclude by summarizing:
- Detected archetype and domains
- Number of actors and capabilities identified
- Number of seed assertions loaded
- Next step: Run `/interview` to begin extracting assertions
