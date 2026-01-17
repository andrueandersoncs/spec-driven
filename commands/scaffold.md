---
description: Generate project infrastructure to make generated code runnable
argument-hint: [force]
allowed-tools: Read, Write, Bash, AskUserQuestion, Glob
model: sonnet
---

# Project Scaffolding

Generate all infrastructure needed to run, test, and build generated code.

## Prerequisites

Check that generated code exists:
- `src/` directory with generated TypeScript files
- `specs/assertions.json` with confirmed assertions

If no generated code exists, instruct user to run `/generate` first.

## Archetype Detection

Read `specs/assertions.json` to determine the software archetype:
- CLI Tool
- Library
- Web Service
- Data Pipeline
- Desktop App

The archetype determines specific scaffolding choices.

## Auto-Detection from Specs

Analyze `specs/assertions.json` and `specs/dafny/*.dfy` to determine:

**Dependencies** (from assertion patterns):
- State machines detected → no extra deps (pure TypeScript)
- Validation patterns → `zod`
- Effect types mentioned → `effect`
- API/HTTP patterns → `hono` (web service archetype)
- CLI patterns → no extra deps (Bun has built-in)

**Testing** (always included):
- Bun's built-in test runner
- Property testing if contracts exist

## Generated Files

### package.json

```json
{
  "name": "[project-name from directory]",
  "version": "0.1.0",
  "type": "module",
  "scripts": {
    "dev": "bun run --watch src/index.ts",
    "build": "bun build src/index.ts --outdir dist --target node",
    "test": "bun test",
    "test:watch": "bun test --watch",
    "typecheck": "tsc --noEmit",
    "verify": "dafny verify specs/dafny/*.dfy && tlc specs/tla/behavior.tla -config specs/tla/behavior.cfg",
    "generate": "bun run scripts/generate.ts"
  },
  "dependencies": {
    // Auto-detected from specs
  },
  "devDependencies": {
    "@types/bun": "latest",
    "typescript": "^5.0.0"
  }
}
```

Archetype-specific additions:
- **CLI Tool**: Add `"bin": { "[name]": "dist/cli.js" }`
- **Web Service**: Add `hono`, start script
- **Library**: Add `"exports"`, `"types"`, build for npm

### tsconfig.json

```json
{
  "compilerOptions": {
    "target": "ESNext",
    "module": "ESNext",
    "moduleResolution": "bundler",
    "strict": true,
    "noUncheckedIndexedAccess": true,
    "noImplicitOverride": true,
    "exactOptionalPropertyTypes": true,
    "skipLibCheck": true,
    "declaration": true,
    "outDir": "dist",
    "rootDir": "src"
  },
  "include": ["src/**/*", "tests/**/*"],
  "exclude": ["node_modules", "dist"]
}
```

### bunfig.toml

```toml
[test]
coverage = true
coverageDir = "coverage"
```

### Entry Point

**CLI Tool** (`src/index.ts`):
```typescript
#!/usr/bin/env bun
/**
 * @generated scaffold
 * Entry point for [project-name] CLI
 */
import { parseArgs } from 'util';
// Import from generated domain code

const { values, positionals } = parseArgs({
  args: Bun.argv.slice(2),
  options: {
    help: { type: 'boolean', short: 'h' },
    // Add options based on domain operations
  },
  allowPositionals: true
});

if (values.help) {
  console.log('Usage: [name] [options] [command]');
  process.exit(0);
}

// Wire up domain logic based on specs
```

**Web Service** (`src/index.ts`):
```typescript
/**
 * @generated scaffold
 * Entry point for [project-name] web service
 */
import { Hono } from 'hono';
import { logger } from 'hono/logger';
// Import from generated domain code

const app = new Hono();
app.use('*', logger());

// Wire up API routes based on generated handlers

export default {
  port: process.env.PORT || 3000,
  fetch: app.fetch
};
```

**Library** (`src/index.ts`):
```typescript
/**
 * @generated scaffold
 * Public API for [project-name] library
 */
// Re-export public types and functions from domain
export * from './types';
export * from './domain';
export * from './validation';
```

### .env.example

Generate from spec constraints:
```bash
# Environment configuration for [project-name]
# Generated from specs/assertions.json

# Required environment variables
NODE_ENV=development

# Add any env vars inferred from specs
# e.g., DATABASE_URL if persistence assertions exist
```

### .gitignore

```
node_modules/
dist/
coverage/
.env
.env.local
*.log

# Claude Code local settings
.claude/*.local.md
```

### README Section

Append to existing README.md or create if missing:

```markdown
## Development

### Prerequisites

- [Bun](https://bun.sh) v1.0+
- Dafny (for verification): `brew install dafny` or via nix
- TLC (for model checking): included in tla2tools.jar

### Quick Start

```bash
# Install dependencies
bun install

# Run tests
bun test

# Start development (with hot reload)
bun run dev

# Type check
bun run typecheck

# Verify specifications
bun run verify
```

### Spec-Driven Workflow

This project uses specification-driven development:

1. **Modify specs** in `specs/dafny/` or `specs/tla/`
2. **Verify** with `bun run verify` or `/verify`
3. **Regenerate** with `/generate`
4. **Test** with `bun test`

All generated code includes `@source-assertion` comments linking to specifications.
```

## Force Mode

If `$ARGUMENTS` contains "force":
- Overwrite existing files
- Skip confirmation prompts

Otherwise:
- Warn before overwriting existing package.json
- Ask user to confirm overwrites

## Scaffold Summary

After generating, report:

```
Project Scaffolded
==================
Created:
  ✓ package.json (dependencies: zod, hono)
  ✓ tsconfig.json (strict mode)
  ✓ bunfig.toml (test coverage enabled)
  ✓ src/index.ts (CLI entry point)
  ✓ .env.example
  ✓ .gitignore

Next Steps:
  1. bun install        # Install dependencies
  2. bun test          # Run generated tests
  3. bun run dev       # Start development server

Tip: Run /test to execute tests with assertion coverage report
```

## Integration with Workflow

After scaffolding completes, the full workflow becomes:

```
/probe-domain → /interview → /verify → /generate → /scaffold → /test → /dev
```

The user now has a runnable project.
