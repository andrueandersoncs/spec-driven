---
name: deployment-patterns
version: 0.1.0
description: This skill provides Docker deployment patterns for spec-driven TypeScript applications. Use when generating Dockerfiles, docker-compose configurations, health checks, or containerizing Bun applications. Triggers on "Docker", "containerize", "deploy", "Dockerfile", "docker-compose", "health check", "production deployment".
---

# Deployment Patterns

Generate production-ready Docker deployments for spec-driven TypeScript applications.

## Core Principles

1. **Multi-stage builds** - Separate build and runtime stages
2. **Minimal images** - Use slim/distroless bases
3. **Non-root execution** - Security by default
4. **Health checks** - Derived from specifications
5. **Environment-based config** - No secrets in images

## Bun Dockerfile Patterns

### Web Service (Production)

```dockerfile
# syntax=docker/dockerfile:1
# @generated from specs

# Build stage
FROM oven/bun:1 AS builder
WORKDIR /app

# Install dependencies first (layer caching)
COPY package.json bun.lockb ./
RUN bun install --frozen-lockfile --production=false

# Copy source and build
COPY src/ ./src/
COPY tsconfig.json ./
RUN bun build src/index.ts --outdir dist --target bun --minify

# Production stage
FROM oven/bun:1-slim AS production
WORKDIR /app

# Copy only production artifacts
COPY --from=builder /app/dist ./dist
COPY --from=builder /app/node_modules ./node_modules
COPY package.json ./

# Security: non-root user
USER bun

# Health check
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

# Install minimal dependencies for Bun binary
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

### Basic Web Service

```yaml
# docker-compose.yml
version: '3.8'

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
version: '3.8'

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
version: '3.8'

services:
  app:
    build:
      context: .
      target: builder  # Use builder stage with dev deps
    ports:
      - "${PORT:-3000}:3000"
    volumes:
      - ./src:/app/src:ro  # Mount source for hot reload
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
  // checks.externalApi = await checkExternalApi();

  const hasFailure = Object.values(checks).some(c => c.status === 'fail');

  return {
    status: hasFailure ? 'unhealthy' : 'ok',
    timestamp: new Date().toISOString(),
    checks
  };
}
```

### Health Check with Dependencies

```typescript
// src/health.ts
// Generated from specs with database/cache assertions

async function checkDatabase(): Promise<CheckResult> {
  const start = Date.now();
  try {
    await db.query('SELECT 1');
    return { status: 'ok', latency: Date.now() - start };
  } catch (e) {
    return { status: 'fail', message: String(e) };
  }
}

async function checkCache(): Promise<CheckResult> {
  const start = Date.now();
  try {
    await cache.ping();
    return { status: 'ok', latency: Date.now() - start };
  } catch (e) {
    return { status: 'fail', message: String(e) };
  }
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
LABEL com.spec-driven.dafny-verified="true"
LABEL com.spec-driven.tlc-verified="true"
```

## Security Hardening

### Non-Root User

```dockerfile
# Create non-root user
RUN useradd -r -s /bin/false -u 1001 appuser

# Set ownership
RUN chown -R appuser:appuser /app

# Switch to non-root
USER appuser
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

## Examples

See `examples/` for complete configurations:
- `web-service/` - Full web service deployment
- `cli-tool/` - CLI binary distribution
- `data-pipeline/` - Scheduled job deployment
