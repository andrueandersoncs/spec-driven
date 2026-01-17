# syntax=docker/dockerfile:1
# Enables BuildKit features. See: https://docs.docker.com/build/buildkit/
#
# @generated from specs
# CLI tool Dockerfile - compiles to standalone binary
#
# Reference: https://docs.docker.com/reference/dockerfile/
# Best practices: https://docs.docker.com/build/building/best-practices/

# Build stage - multi-stage build for minimal production image
# See: https://docs.docker.com/build/building/multi-stage/
FROM oven/bun:1 AS builder
WORKDIR /app

# Install dependencies first for better layer caching
# See: https://docs.docker.com/build/cache/#order-your-layers
COPY package.json bun.lockb ./
RUN bun install --frozen-lockfile

COPY src/ ./src/
COPY tsconfig.json ./

# Compile to standalone binary for minimal runtime footprint
RUN bun build src/index.ts --compile --outfile dist/cli

# Minimal runtime - just the binary, no runtime dependencies
# See: https://docs.docker.com/build/building/best-practices/#use-multi-stage-builds
FROM debian:bookworm-slim AS production

# Install only essential dependencies and clean up in same layer
# See: https://docs.docker.com/build/building/best-practices/#apt-get
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/dist/cli /usr/local/bin/app

# Non-root user for security - use explicit UID for consistency
# See: https://docs.docker.com/reference/dockerfile/#user
RUN useradd -r -s /bin/false -u 1001 appuser
USER appuser

# OCI image labels for metadata and traceability
# See: https://docs.docker.com/reference/dockerfile/#label
# Spec: https://github.com/opencontainers/image-spec/blob/main/annotations.md
LABEL org.opencontainers.image.title="spec-driven-cli"
LABEL com.spec-driven.verified="true"

ENTRYPOINT ["app"]
