---
description: Generate Docker deployment artifacts from specifications
argument-hint: [build|push]
allowed-tools: Read, Write, Bash, Glob, AskUserQuestion
model: sonnet
---

# Deployment Artifact Generation

Generate Docker-based deployment artifacts derived from specifications.

## Prerequisites

Check project is ready for deployment:
- `package.json` exists
- Tests pass (`bun test` exits 0)
- Specifications verified (`specs/assertions.json` has all confirmed)

If not ready:
```
Deployment Checklist
====================
❌ Tests not passing - run /test first
❌ Specs not verified - run /verify first
✅ Package.json exists

Fix issues before deploying.
```

## Archetype Detection

Read `specs/assertions.json` to determine archetype-specific deployment:

| Archetype | Deployment Pattern |
|-----------|-------------------|
| CLI Tool | Single binary, multi-arch |
| Web Service | HTTP server, health checks |
| Library | NPM package (not Docker) |
| Data Pipeline | Scheduled job, idempotent |

## Generated Artifacts

### Dockerfile

**Web Service:**

```dockerfile
# Dockerfile
# @generated from specs
# Assertions verified: 2024-01-15T10:30:00Z

# Build stage
FROM oven/bun:1 AS builder
WORKDIR /app

# Copy package files
COPY package.json bun.lockb ./
RUN bun install --frozen-lockfile

# Copy source and build
COPY src/ ./src/
COPY tsconfig.json ./
RUN bun build src/index.ts --outdir dist --target bun

# Production stage
FROM oven/bun:1-slim AS production
WORKDIR /app

# Copy built artifacts
COPY --from=builder /app/dist ./dist
COPY --from=builder /app/node_modules ./node_modules
COPY package.json ./

# Non-root user for security
USER bun

# Health check derived from specs
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
  CMD curl -f http://localhost:${PORT:-3000}/health || exit 1

# Expose port
EXPOSE ${PORT:-3000}

# Start server
CMD ["bun", "run", "dist/index.js"]
```

**CLI Tool:**

```dockerfile
# Dockerfile
# @generated from specs

FROM oven/bun:1 AS builder
WORKDIR /app

COPY package.json bun.lockb ./
RUN bun install --frozen-lockfile

COPY src/ ./src/
COPY tsconfig.json ./
RUN bun build src/index.ts --compile --outfile dist/cli

# Minimal runtime
FROM debian:bookworm-slim AS production
WORKDIR /app

COPY --from=builder /app/dist/cli /usr/local/bin/[project-name]

ENTRYPOINT ["[project-name]"]
```

**Data Pipeline:**

```dockerfile
# Dockerfile
# @generated from specs

FROM oven/bun:1 AS builder
WORKDIR /app

COPY package.json bun.lockb ./
RUN bun install --frozen-lockfile

COPY src/ ./src/
COPY tsconfig.json ./

FROM oven/bun:1-slim AS production
WORKDIR /app

COPY --from=builder /app/node_modules ./node_modules
COPY --from=builder /app/src ./src
COPY package.json ./

# Pipeline runs once and exits
CMD ["bun", "run", "src/index.ts"]
```

### docker-compose.yml

```yaml
# docker-compose.yml
# @generated from specs

services:
  app:
    build: .
    ports:
      - "${PORT:-3000}:3000"
    environment:
      - NODE_ENV=production
      # Environment variables derived from specs
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:3000/health"]
      interval: 30s
      timeout: 3s
      retries: 3
    restart: unless-stopped

# Add services if specs indicate dependencies
# e.g., if persistence assertions exist:
#  db:
#    image: postgres:16
#    volumes:
#      - pgdata:/var/lib/postgresql/data
#    environment:
#      - POSTGRES_DB=[project-name]
#      - POSTGRES_USER=app
#      - POSTGRES_PASSWORD=${DB_PASSWORD}
#
#volumes:
#  pgdata:
```

### .dockerignore

```
# .dockerignore
node_modules
dist
coverage
.git
.github
*.log
.env
.env.*
!.env.example
specs/
tests/
*.md
.claude/
```

## Health Check Derivation

From specs, derive health check requirements:

1. **Basic health** (always included):
   - Server responds to HTTP
   - Process is running

2. **From assertions** (if present):
   - If database assertions → check DB connection
   - If external API assertions → check API reachability
   - If queue assertions → check queue connection

Generate health check endpoint if not exists:

```typescript
// src/health.ts
// @generated for deployment

export const healthCheck = async () => {
  const checks = {
    status: 'ok' as const,
    timestamp: new Date().toISOString(),
    checks: {} as Record<string, boolean>
  };

  // Add checks based on spec dependencies
  // checks.database = await checkDatabase();
  // checks.externalApi = await checkExternalApi();

  return checks;
};
```

## Build and Push

### Local Build

If `$ARGUMENTS` contains "build":

```bash
docker build -t [project-name]:latest .
```

Report:
```
Docker Build Complete
=====================
Image: [project-name]:latest
Size: 45MB
Layers: 12

To run locally:
  docker run -p 3000:3000 [project-name]:latest

To run with docker-compose:
  docker-compose up
```

### Push to Registry

If `$ARGUMENTS` contains "push":

First, ask for registry:

**Question**: "Which container registry should I push to?"
**Options**:
- Docker Hub (docker.io/username/[project-name])
- GitHub Container Registry (ghcr.io/username/[project-name])
- Custom registry (enter URL)

Then:
```bash
docker tag [project-name]:latest [registry]/[project-name]:latest
docker push [registry]/[project-name]:latest
```

## Verification Metadata

Include verification metadata in Docker labels:

```dockerfile
LABEL org.opencontainers.image.title="[project-name]"
LABEL org.opencontainers.image.description="[from specs]"
LABEL org.opencontainers.image.version="0.1.0"
LABEL com.spec-driven.verified="true"
LABEL com.spec-driven.verified-at="2024-01-15T10:30:00Z"
LABEL com.spec-driven.assertions="3"
LABEL com.spec-driven.dafny-verified="true"
LABEL com.spec-driven.tlc-verified="true"
```

## Security Considerations

From specs, apply security patterns:

1. **Non-root user**: Always run as non-root
2. **Minimal image**: Use slim/distroless bases
3. **No secrets in image**: Use environment variables
4. **Read-only filesystem**: If specs allow

```dockerfile
# Security hardening
USER bun
RUN chmod -R 555 /app

# Read-only root filesystem (if applicable)
# Requires writable /tmp for some operations
```

## Deployment Summary

After generating:

```
Deployment Artifacts Generated
==============================
Created:
  ✓ Dockerfile (multi-stage, 45MB)
  ✓ docker-compose.yml
  ✓ .dockerignore
  ✓ src/health.ts (health check endpoint)

Verification Status:
  ✓ Dafny specs verified
  ✓ TLC model checked
  ✓ All tests passing
  ✓ 3/3 assertions confirmed

Next Steps:
  1. docker build -t [project-name] .
  2. docker run -p 3000:3000 [project-name]
  3. curl http://localhost:3000/health

Or use docker-compose:
  docker-compose up

Production deployment:
  • Set environment variables in production
  • Use secrets management for sensitive values
  • Configure logging and monitoring
```

## Library Archetype (No Docker)

For library archetype, skip Docker and suggest npm publishing:

```
Library Deployment
==================
Libraries are typically published to npm, not Docker.

Generated:
  ✓ package.json (exports configured)
  ✓ tsconfig.json (declarations enabled)

To publish:
  1. bun run build
  2. npm publish

Or for private packages:
  1. npm publish --registry https://your-registry
```
