# syntax=docker/dockerfile:1
# @generated from specs
# CLI tool Dockerfile - compiles to standalone binary

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

# Non-root user for security
RUN useradd -r -s /bin/false appuser
USER appuser

# Verification metadata
LABEL org.opencontainers.image.title="spec-driven-cli"
LABEL com.spec-driven.verified="true"

ENTRYPOINT ["app"]
