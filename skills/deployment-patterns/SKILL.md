---
name: deployment-patterns
version: 0.1.0
description: This skill should be used when deploying spec-driven TypeScript applications, generating Docker configurations, or when the user asks "create Dockerfile", "write docker-compose", "containerize this app", "add health checks", "deploy to production", "generate deployment files", "Bun Docker image", "multi-stage build", or "Docker security hardening".
---

# Deployment Patterns

Generate production-ready Docker deployments for spec-driven TypeScript applications.

## Core Principles

1. **[Multi-stage builds](https://docs.docker.com/build/building/multi-stage/)** - Separate build and runtime stages for smaller, more secure images
2. **Minimal images** - Use slim/distroless bases to reduce attack surface
3. **[Non-root execution](https://docs.docker.com/engine/security/#linux-kernel-capabilities)** - Security by default; containers don't need real root privileges
4. **[Health checks](https://docs.docker.com/reference/dockerfile/#healthcheck)** - Derived from specifications for orchestrator integration
5. **Environment-based config** - No secrets in images; use runtime environment variables

## Bun Dockerfile Patterns

> **Reference**: [Dockerfile reference](https://docs.docker.com/reference/dockerfile/) | [Best practices](https://docs.docker.com/build/building/best-practices/)

### Web Service (Production)

```dockerfile
# syntax=docker/dockerfile:1
# Enables BuildKit features. See: https://docs.docker.com/build/buildkit/
# @generated from specs

# Build stage - see: https://docs.docker.com/build/building/multi-stage/
FROM oven/bun:1 AS builder
WORKDIR /app

# Install dependencies first for better layer caching
# See: https://docs.docker.com/build/cache/#order-your-layers
COPY package.json bun.lockb ./
RUN bun install --frozen-lockfile --production=false

# Copy source and build
COPY src/ ./src/
COPY tsconfig.json ./
RUN bun build src/index.ts --outdir dist --target bun --minify

# Production stage - use slim image to reduce attack surface
# See: https://docs.docker.com/build/building/best-practices/#use-multi-stage-builds
FROM oven/bun:1-slim AS production
WORKDIR /app

# Copy only production artifacts
COPY --from=builder /app/dist ./dist
COPY --from=builder /app/node_modules ./node_modules
COPY package.json ./

# Security: run as non-root user
# See: https://docs.docker.com/reference/dockerfile/#user
USER bun

# Health check for container orchestration
# See: https://docs.docker.com/reference/dockerfile/#healthcheck
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

> **Reference**: [Compose file reference](https://docs.docker.com/reference/compose-file/) | [Compose specification](https://docs.docker.com/reference/compose-file/version-and-name/)
>
> **Note**: The `version` field is [obsolete](https://docs.docker.com/reference/compose-file/version-and-name/) and should be omitted. Docker Compose always uses the most recent schema.

### Basic Web Service

```yaml
# docker-compose.yml
# Note: version field is obsolete and omitted
# See: https://docs.docker.com/reference/compose-file/version-and-name/

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
    # See: https://docs.docker.com/reference/compose-file/services/#healthcheck
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:3000/health"]
      interval: 30s
      timeout: 3s
      retries: 3
    restart: unless-stopped  # See: https://docs.docker.com/reference/compose-file/services/#restart
```

### With Database (from spec assertions)

```yaml
# docker-compose.yml
# Generated because specs include persistence assertions
# Note: version field is obsolete and omitted

services:
  app:
    build: .
    ports:
      - "${PORT:-3000}:3000"
    environment:
      - NODE_ENV=production
      - DATABASE_URL=postgresql://app:${DB_PASSWORD}@db:5432/appdb
    # Wait for db healthcheck before starting
    # See: https://docs.docker.com/reference/compose-file/services/#depends_on
    depends_on:
      db:
        condition: service_healthy
    restart: unless-stopped

  db:
    image: postgres:16-alpine
    # Named volumes for data persistence
    # See: https://docs.docker.com/reference/compose-file/volumes/
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
# Note: version field is obsolete and omitted

services:
  app:
    build:
      context: .
      target: builder  # Use builder stage with dev deps
    ports:
      - "${PORT:-3000}:3000"
    # Bind mount for development hot reload
    # See: https://docs.docker.com/reference/compose-file/services/#volumes
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

> **Reference**: [Docker security overview](https://docs.docker.com/engine/security/) | [Security best practices](https://docs.docker.com/build/building/best-practices/#user)

### Non-Root User

Running containers as non-root users provides defense-in-depth. Even if an attacker escalates privileges within the container, they have far fewer capabilities than real root.

```dockerfile
# Create non-root user with explicit UID for consistency
# See: https://docs.docker.com/reference/dockerfile/#user
RUN useradd -r -s /bin/false -u 1001 appuser

# Set ownership of application files
RUN chown -R appuser:appuser /app

# Switch to non-root user for runtime
USER appuser
```

### Read-Only Filesystem

Prevents runtime modification of the container filesystem, limiting attacker capabilities.

```yaml
# docker-compose.yml
# See: https://docs.docker.com/reference/compose-file/services/#read_only
services:
  app:
    read_only: true
    # tmpfs mounts for writable directories that need to exist
    # See: https://docs.docker.com/reference/compose-file/services/#tmpfs
    tmpfs:
      - /tmp
    volumes:
      - type: tmpfs
        target: /app/tmp
```

### Resource Limits

Prevents denial-of-service attacks and ensures fair resource distribution in multi-container environments.

```yaml
# docker-compose.yml
# See: https://docs.docker.com/reference/compose-file/deploy/#resources
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

> **Reference**: [.dockerignore documentation](https://docs.docker.com/build/concepts/context/#dockerignore-files)

Exclude unnecessary files from the build context to speed up builds and reduce image size.

```gitignore
# .dockerignore
# Exclude development and test artifacts
node_modules
*.log
.git
.gitignore
coverage/
tests/
*.test.ts
*.spec.ts

# Exclude documentation and config
README.md
CHANGELOG.md
.env
.env.*
!.env.example

# Exclude build tools
.github/
.vscode/
*.md

# Exclude specs (not needed at runtime)
specs/
generated/
```

## Additional Resources

### Reference Files

For comprehensive Docker documentation and patterns:
- **`references/docker-reference.md`** - Complete Docker reference for Bun applications including Dockerfile instructions, multi-stage builds, Compose configuration, health checks, and security best practices

### Example Files

Working examples ready to copy and customize:
- **`examples/Dockerfile.web-service`** - Production-ready web service Dockerfile
- **`examples/Dockerfile.cli`** - CLI tool compiled binary Dockerfile
- **`examples/docker-compose.yml`** - Full production deployment with PostgreSQL
- **`examples/docker-compose.dev.yml`** - Development environment with hot reloading
- **`examples/health.ts`** - Health check endpoint implementation

## Docker Documentation References

### Dockerfile

| Topic | Documentation |
|-------|---------------|
| Dockerfile reference | https://docs.docker.com/reference/dockerfile/ |
| Best practices | https://docs.docker.com/build/building/best-practices/ |
| Multi-stage builds | https://docs.docker.com/build/building/multi-stage/ |
| BuildKit | https://docs.docker.com/build/buildkit/ |
| Build cache | https://docs.docker.com/build/cache/ |
| .dockerignore | https://docs.docker.com/build/concepts/context/#dockerignore-files |

### Dockerfile Instructions

| Instruction | Documentation |
|-------------|---------------|
| FROM | https://docs.docker.com/reference/dockerfile/#from |
| USER | https://docs.docker.com/reference/dockerfile/#user |
| HEALTHCHECK | https://docs.docker.com/reference/dockerfile/#healthcheck |
| LABEL | https://docs.docker.com/reference/dockerfile/#label |
| COPY | https://docs.docker.com/reference/dockerfile/#copy |
| RUN | https://docs.docker.com/reference/dockerfile/#run |
| CMD | https://docs.docker.com/reference/dockerfile/#cmd |
| ENTRYPOINT | https://docs.docker.com/reference/dockerfile/#entrypoint |

### Docker Compose

| Topic | Documentation |
|-------|---------------|
| Compose file reference | https://docs.docker.com/reference/compose-file/ |
| Services configuration | https://docs.docker.com/reference/compose-file/services/ |
| Version field (obsolete) | https://docs.docker.com/reference/compose-file/version-and-name/ |
| Volumes | https://docs.docker.com/reference/compose-file/volumes/ |
| Networks | https://docs.docker.com/reference/compose-file/networks/ |

### Compose Service Options

| Option | Documentation |
|--------|---------------|
| healthcheck | https://docs.docker.com/reference/compose-file/services/#healthcheck |
| depends_on | https://docs.docker.com/reference/compose-file/services/#depends_on |
| deploy (resources) | https://docs.docker.com/reference/compose-file/deploy/#resources |
| read_only | https://docs.docker.com/reference/compose-file/services/#read_only |
| restart | https://docs.docker.com/reference/compose-file/services/#restart |
| tmpfs | https://docs.docker.com/reference/compose-file/services/#tmpfs |
| volumes | https://docs.docker.com/reference/compose-file/services/#volumes |

### Security

| Topic | Documentation |
|-------|---------------|
| Docker security overview | https://docs.docker.com/engine/security/ |
| Content trust | https://docs.docker.com/engine/security/trust/ |
| Seccomp profiles | https://docs.docker.com/engine/security/seccomp/ |
| AppArmor profiles | https://docs.docker.com/engine/security/apparmor/ |

### OCI Standards

| Topic | Documentation |
|-------|---------------|
| Image labels spec | https://github.com/opencontainers/image-spec/blob/main/annotations.md |
