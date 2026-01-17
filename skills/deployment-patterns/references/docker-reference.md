# Docker Reference for Bun Applications

Comprehensive Docker reference for deploying spec-driven TypeScript applications with Bun.

> **Source**: [Docker Documentation](https://docs.docker.com/)

## Table of Contents

- [Dockerfile Instructions](#dockerfile-instructions)
- [Multi-Stage Builds](#multi-stage-builds)
- [Docker Compose Reference](#docker-compose-reference)
- [Health Checks](#health-checks)
- [Security Best Practices](#security-best-practices)
- [Bun-Specific Patterns](#bun-specific-patterns)

---

## Dockerfile Instructions

### Essential Instructions

| Instruction | Purpose | Documentation |
|-------------|---------|---------------|
| `FROM` | Set base image | [docs.docker.com/reference/dockerfile/#from](https://docs.docker.com/reference/dockerfile/#from) |
| `WORKDIR` | Set working directory | [docs.docker.com/reference/dockerfile/#workdir](https://docs.docker.com/reference/dockerfile/#workdir) |
| `COPY` | Copy files into image | [docs.docker.com/reference/dockerfile/#copy](https://docs.docker.com/reference/dockerfile/#copy) |
| `RUN` | Execute command | [docs.docker.com/reference/dockerfile/#run](https://docs.docker.com/reference/dockerfile/#run) |
| `ENV` | Set environment variable | [docs.docker.com/reference/dockerfile/#env](https://docs.docker.com/reference/dockerfile/#env) |
| `EXPOSE` | Document port | [docs.docker.com/reference/dockerfile/#expose](https://docs.docker.com/reference/dockerfile/#expose) |
| `USER` | Set runtime user | [docs.docker.com/reference/dockerfile/#user](https://docs.docker.com/reference/dockerfile/#user) |
| `CMD` | Default command | [docs.docker.com/reference/dockerfile/#cmd](https://docs.docker.com/reference/dockerfile/#cmd) |
| `ENTRYPOINT` | Fixed command | [docs.docker.com/reference/dockerfile/#entrypoint](https://docs.docker.com/reference/dockerfile/#entrypoint) |
| `HEALTHCHECK` | Container health | [docs.docker.com/reference/dockerfile/#healthcheck](https://docs.docker.com/reference/dockerfile/#healthcheck) |
| `LABEL` | Metadata | [docs.docker.com/reference/dockerfile/#label](https://docs.docker.com/reference/dockerfile/#label) |

### COPY vs ADD

```dockerfile
# COPY - Simple file copying (preferred)
COPY package.json bun.lockb ./
COPY src/ ./src/

# ADD - Has extra features (URL fetch, tar extraction)
# Only use when you need those features
ADD https://example.com/file.tar.gz /app/
```

### CMD vs ENTRYPOINT

```dockerfile
# CMD - Default command, can be overridden
CMD ["bun", "run", "start"]

# ENTRYPOINT - Fixed command, CMD becomes arguments
ENTRYPOINT ["bun"]
CMD ["run", "start"]

# Running: docker run myimage run test
# Executes: bun run test
```

---

## Multi-Stage Builds

Multi-stage builds reduce final image size by separating build and runtime environments.

> **Reference**: [docs.docker.com/build/building/multi-stage/](https://docs.docker.com/build/building/multi-stage/)

### Basic Pattern

```dockerfile
# syntax=docker/dockerfile:1

# Stage 1: Build
FROM oven/bun:1 AS builder
WORKDIR /app
COPY package.json bun.lockb ./
RUN bun install --frozen-lockfile
COPY src/ ./src/
COPY tsconfig.json ./
RUN bun build src/index.ts --outdir dist --target bun

# Stage 2: Production
FROM oven/bun:1-slim AS production
WORKDIR /app
COPY --from=builder /app/dist ./dist
COPY --from=builder /app/node_modules ./node_modules
COPY package.json ./
USER bun
CMD ["bun", "run", "dist/index.js"]
```

### Named Stages

```dockerfile
# Reference stages by name
COPY --from=builder /app/dist ./dist

# Or by index (0-based)
COPY --from=0 /app/dist ./dist
```

### Build Specific Stage

```bash
# Build only the builder stage
docker build --target builder -t myapp:build .

# Build production stage (default)
docker build --target production -t myapp:prod .
```

---

## Docker Compose Reference

> **Reference**: [docs.docker.com/reference/compose-file/](https://docs.docker.com/reference/compose-file/)

### Important Note

The `version` field is **obsolete** and should be omitted. Docker Compose automatically uses the latest schema.

> **Source**: [docs.docker.com/reference/compose-file/version-and-name/](https://docs.docker.com/reference/compose-file/version-and-name/)

### Service Configuration

```yaml
# docker-compose.yml
services:
  app:
    build:
      context: .
      dockerfile: Dockerfile
      target: production

    image: myapp:latest
    container_name: myapp

    ports:
      - "${PORT:-3000}:3000"

    environment:
      - NODE_ENV=production
      - DATABASE_URL=${DATABASE_URL}

    env_file:
      - .env

    volumes:
      - ./data:/app/data
      - logs:/app/logs

    depends_on:
      db:
        condition: service_healthy

    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:3000/health"]
      interval: 30s
      timeout: 3s
      retries: 3
      start_period: 10s

    restart: unless-stopped

    deploy:
      resources:
        limits:
          cpus: '1'
          memory: 512M
        reservations:
          cpus: '0.25'
          memory: 128M

volumes:
  logs:
```

### Dependency Conditions

```yaml
depends_on:
  db:
    condition: service_started     # Default: just start
    condition: service_healthy     # Wait for healthcheck
    condition: service_completed_successfully  # For init containers
```

### Volume Types

```yaml
volumes:
  # Named volume (managed by Docker)
  - pgdata:/var/lib/postgresql/data

  # Bind mount (host path)
  - ./src:/app/src:ro

  # tmpfs (in-memory)
  - type: tmpfs
    target: /tmp
```

---

## Health Checks

> **Reference**: [docs.docker.com/reference/dockerfile/#healthcheck](https://docs.docker.com/reference/dockerfile/#healthcheck)

### Dockerfile HEALTHCHECK

```dockerfile
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
  CMD curl -f http://localhost:3000/health || exit 1
```

### Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `--interval` | 30s | Time between checks |
| `--timeout` | 30s | Time before check is considered failed |
| `--start-period` | 0s | Grace period for container startup |
| `--retries` | 3 | Consecutive failures before unhealthy |

### Health Check Commands

```dockerfile
# HTTP endpoint (requires curl)
HEALTHCHECK CMD curl -f http://localhost:3000/health || exit 1

# TCP port check (requires nc)
HEALTHCHECK CMD nc -z localhost 3000 || exit 1

# Custom script
HEALTHCHECK CMD /app/healthcheck.sh

# Bun script
HEALTHCHECK CMD bun run dist/health.js || exit 1
```

### Compose Health Check

```yaml
healthcheck:
  test: ["CMD", "curl", "-f", "http://localhost:3000/health"]
  # Or shell form
  test: curl -f http://localhost:3000/health || exit 1
  interval: 30s
  timeout: 3s
  retries: 3
  start_period: 10s
```

---

## Security Best Practices

> **Reference**: [docs.docker.com/engine/security/](https://docs.docker.com/engine/security/)

### Non-Root User

```dockerfile
# Create non-root user
RUN useradd -r -s /bin/false -u 1001 appuser

# Set ownership
RUN chown -R appuser:appuser /app

# Switch to non-root
USER appuser
```

For Bun images:
```dockerfile
# Bun images include a 'bun' user
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

### Security Options

```yaml
# docker-compose.yml
services:
  app:
    security_opt:
      - no-new-privileges:true
    cap_drop:
      - ALL
    cap_add:
      - NET_BIND_SERVICE  # If needed for ports < 1024
```

### .dockerignore

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
.env
.env.*
!.env.example
.github/
.vscode/
specs/
generated/
```

---

## Bun-Specific Patterns

### Official Bun Images

| Image | Size | Use Case |
|-------|------|----------|
| `oven/bun:1` | ~150MB | Build stage, development |
| `oven/bun:1-slim` | ~100MB | Production runtime |
| `oven/bun:1-alpine` | ~70MB | Minimal production |
| `oven/bun:1-debian` | ~150MB | When glibc required |

### Bun Build Commands

```dockerfile
# Bundle for production
RUN bun build src/index.ts --outdir dist --target bun --minify

# Compile to standalone binary
RUN bun build src/index.ts --compile --outfile dist/app
```

### Bun Install Flags

```dockerfile
# Production install (no devDependencies)
RUN bun install --frozen-lockfile --production

# Full install (including devDependencies for build)
RUN bun install --frozen-lockfile
```

### Layer Caching for Bun

```dockerfile
# Copy lockfile first for better caching
COPY package.json bun.lockb ./
RUN bun install --frozen-lockfile

# Then copy source (changes more frequently)
COPY src/ ./src/
```

### Compiled Binary Pattern

```dockerfile
# Build stage
FROM oven/bun:1 AS builder
WORKDIR /app
COPY package.json bun.lockb ./
RUN bun install --frozen-lockfile
COPY src/ ./src/
RUN bun build src/index.ts --compile --outfile dist/app

# Minimal runtime (just the binary)
FROM debian:bookworm-slim AS production
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates && rm -rf /var/lib/apt/lists/*
COPY --from=builder /app/dist/app /usr/local/bin/app
RUN useradd -r -s /bin/false appuser
USER appuser
ENTRYPOINT ["app"]
```

---

## Quick Reference Links

### Dockerfile

- [Dockerfile Reference](https://docs.docker.com/reference/dockerfile/)
- [Best Practices](https://docs.docker.com/build/building/best-practices/)
- [Multi-Stage Builds](https://docs.docker.com/build/building/multi-stage/)
- [Build Cache](https://docs.docker.com/build/cache/)
- [BuildKit](https://docs.docker.com/build/buildkit/)

### Docker Compose

- [Compose File Reference](https://docs.docker.com/reference/compose-file/)
- [Services](https://docs.docker.com/reference/compose-file/services/)
- [Volumes](https://docs.docker.com/reference/compose-file/volumes/)
- [Networks](https://docs.docker.com/reference/compose-file/networks/)

### Security

- [Security Overview](https://docs.docker.com/engine/security/)
- [Content Trust](https://docs.docker.com/engine/security/trust/)
- [Seccomp Profiles](https://docs.docker.com/engine/security/seccomp/)
- [AppArmor Profiles](https://docs.docker.com/engine/security/apparmor/)

### Bun

- [Bun Documentation](https://bun.sh/docs)
- [Bun Docker Images](https://hub.docker.com/r/oven/bun)
