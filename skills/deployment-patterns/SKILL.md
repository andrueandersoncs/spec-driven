---
name: deployment-patterns
version: 0.1.0
description: This skill should be used when deploying spec-driven TypeScript applications, generating Docker configurations, or when the user asks "create Dockerfile", "write docker-compose", "containerize this app", "add health checks", "deploy to production", "generate deployment files", "Bun Docker image", "multi-stage build", or "Docker security hardening".
---

# Deployment Patterns

Generate production-ready Docker deployments for spec-driven TypeScript applications.

## Core Principles

1. **Multi-stage builds** - Separate build and runtime stages for smaller, more secure images
2. **Minimal images** - Use slim/distroless bases to reduce attack surface
3. **Non-root execution** - Security by default; containers don't need real root privileges
4. **Health checks** - Derived from specifications for orchestrator integration
5. **Environment-based config** - No secrets in images; use runtime environment variables

For comprehensive Docker documentation, see **`references/docker-reference.md`**.

## Bun Dockerfile Patterns

### Web Service (Production)

```dockerfile
# syntax=docker/dockerfile:1
# @generated from specs

# Build stage
FROM oven/bun:1 AS builder
WORKDIR /app

# Install dependencies first for better layer caching
COPY package.json bun.lockb ./
RUN bun install --frozen-lockfile --production=false

# Copy source and build
COPY src/ ./src/
COPY tsconfig.json ./
RUN bun build src/index.ts --outdir dist --target bun --minify

# Production stage - use slim image
FROM oven/bun:1-slim AS production
WORKDIR /app

# Copy only production artifacts
COPY --from=builder /app/dist ./dist
COPY --from=builder /app/node_modules ./node_modules
COPY package.json ./

# Security: run as non-root user
USER bun

# Health check for container orchestration
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
  CMD bun run dist/health.js || exit 1

EXPOSE 3000
CMD ["bun", "run", "dist/index.js"]
```

### CLI Tool (Compiled Binary)

```dockerfile
# syntax=docker/dockerfile:1
# @generated from specs

FROM oven/bun:1 AS builder
WORKDIR /app

COPY package.json bun.lockb ./
RUN bun install --frozen-lockfile

COPY src/ ./src/
COPY tsconfig.json ./

# Compile to standalone binary
RUN bun build src/index.ts --compile --outfile dist/cli

# Minimal runtime (just the binary)
FROM debian:bookworm-slim AS production

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/dist/cli /usr/local/bin/app

# Non-root user
RUN useradd -r -s /bin/false appuser
USER appuser

ENTRYPOINT ["app"]
```

### Data Pipeline (Job)

```dockerfile
# syntax=docker/dockerfile:1
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

USER bun

# Jobs run once and exit
CMD ["bun", "run", "src/index.ts"]
```

## Docker Compose Patterns

> **Note**: The `version` field is obsolete and should be omitted. Docker Compose always uses the most recent schema.

### Basic Web Service

```yaml
# docker-compose.yml
services:
  app:
    build:
      context: .
      dockerfile: Dockerfile
      target: production
    ports:
      - "${PORT:-3000}:3000"
    environment:
      - NODE_ENV=production
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:3000/health"]
      interval: 30s
      timeout: 3s
      retries: 3
    restart: unless-stopped
```

### With Database (from spec assertions)

```yaml
# docker-compose.yml
# Generated because specs include persistence assertions
services:
  app:
    build: .
    ports:
      - "${PORT:-3000}:3000"
    environment:
      - NODE_ENV=production
      - DATABASE_URL=postgresql://app:${DB_PASSWORD}@db:5432/appdb
    depends_on:
      db:
        condition: service_healthy
    restart: unless-stopped

  db:
    image: postgres:16-alpine
    volumes:
      - pgdata:/var/lib/postgresql/data
    environment:
      - POSTGRES_DB=appdb
      - POSTGRES_USER=app
      - POSTGRES_PASSWORD=${DB_PASSWORD}
    healthcheck:
      test: ["CMD-SHELL", "pg_isready -U app -d appdb"]
      interval: 10s
      timeout: 5s
      retries: 5

volumes:
  pgdata:
```

### Development Compose

```yaml
# docker-compose.dev.yml
services:
  app:
    build:
      context: .
      target: builder  # Use builder stage with dev deps
    ports:
      - "${PORT:-3000}:3000"
    volumes:
      - ./src:/app/src:ro  # Mount source read-only for hot reload
    environment:
      - NODE_ENV=development
    command: ["bun", "run", "--watch", "src/index.ts"]
```

## Health Check Patterns

### Basic HTTP Health

```typescript
// src/health.ts
// @generated for deployment

export interface HealthStatus {
  status: 'ok' | 'degraded' | 'unhealthy';
  timestamp: string;
  checks: Record<string, CheckResult>;
}

interface CheckResult {
  status: 'ok' | 'fail';
  latency?: number;
  message?: string;
}

export async function healthCheck(): Promise<HealthStatus> {
  const checks: Record<string, CheckResult> = {};

  // Always check: process is responsive
  checks.process = { status: 'ok' };

  // Add checks based on spec dependencies
  // checks.database = await checkDatabase();
  // checks.cache = await checkCache();

  const hasFailure = Object.values(checks).some(c => c.status === 'fail');

  return {
    status: hasFailure ? 'unhealthy' : 'ok',
    timestamp: new Date().toISOString(),
    checks
  };
}
```

### Hono Health Endpoint

```typescript
// src/api/health.ts
import { Hono } from 'hono';
import { healthCheck } from '../health';

export const healthRoutes = new Hono()
  .get('/health', async (c) => {
    const health = await healthCheck();
    const status = health.status === 'ok' ? 200 : 503;
    return c.json(health, status);
  })
  .get('/ready', async (c) => {
    // Readiness: can accept traffic
    const health = await healthCheck();
    return c.json({ ready: health.status !== 'unhealthy' });
  })
  .get('/live', (c) => {
    // Liveness: process is alive
    return c.json({ alive: true });
  });
```

## Environment Configuration

### .env.example Template

```bash
# .env.example
# Generated from spec assertions

# Required
NODE_ENV=production
PORT=3000

# Database (if persistence assertions exist)
DATABASE_URL=postgresql://user:password@localhost:5432/dbname

# External APIs (if external service assertions exist)
API_KEY=your-api-key
API_URL=https://api.example.com

# Observability
LOG_LEVEL=info
```

### Docker Labels (Metadata)

```dockerfile
# Verification metadata for traceability
LABEL org.opencontainers.image.title="project-name"
LABEL org.opencontainers.image.version="0.1.0"
LABEL com.spec-driven.verified="true"
LABEL com.spec-driven.verified-at="2024-01-15T10:30:00Z"
LABEL com.spec-driven.assertions="5"
```

## Security Hardening

### Non-Root User

```dockerfile
# For custom images: create non-root user with explicit UID
RUN useradd -r -s /bin/false -u 1001 appuser
RUN chown -R appuser:appuser /app
USER appuser

# For Bun images: use built-in 'bun' user
USER bun
```

### Read-Only Filesystem

```yaml
# docker-compose.yml
services:
  app:
    read_only: true
    tmpfs:
      - /tmp
    volumes:
      - type: tmpfs
        target: /app/tmp
```

### Resource Limits

```yaml
# docker-compose.yml
services:
  app:
    deploy:
      resources:
        limits:
          cpus: '1'
          memory: 512M
        reservations:
          cpus: '0.25'
          memory: 128M
```

## Build Context and .dockerignore

```gitignore
# .dockerignore
node_modules
*.log
.git
.gitignore
coverage/
tests/
*.test.ts
*.spec.ts
README.md
CHANGELOG.md
.env
.env.*
!.env.example
.github/
.vscode/
specs/
generated/
```

## Additional Resources

### Reference Files

- **`references/docker-reference.md`** - Complete Docker reference for Bun applications including Dockerfile instructions, multi-stage builds, Compose configuration, health checks, security best practices, and all official documentation links

### Example Files

- **`examples/Dockerfile.web-service`** - Production-ready web service Dockerfile
- **`examples/Dockerfile.cli`** - CLI tool compiled binary Dockerfile
- **`examples/docker-compose.yml`** - Full production deployment with PostgreSQL
- **`examples/docker-compose.dev.yml`** - Development environment with hot reloading
- **`examples/health.ts`** - Health check endpoint implementation
