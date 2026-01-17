# syntax=docker/dockerfile:1
# Enables BuildKit features. See: https://docs.docker.com/build/buildkit/
#
# @generated from specs
# Data pipeline Dockerfile - for batch/stream processing jobs
#
# Reference: https://docs.docker.com/reference/dockerfile/
# Best practices: https://docs.docker.com/build/building/best-practices/

# Build stage - multi-stage build for smaller production images
# See: https://docs.docker.com/build/building/multi-stage/
FROM oven/bun:1 AS builder
WORKDIR /app

# Install dependencies first for better layer caching
# See: https://docs.docker.com/build/cache/#order-your-layers
COPY package.json bun.lockb ./
RUN bun install --frozen-lockfile

COPY src/ ./src/
COPY tsconfig.json ./

# Production stage - use slim image to reduce attack surface
FROM oven/bun:1-slim AS production
WORKDIR /app

COPY --from=builder /app/node_modules ./node_modules
COPY --from=builder /app/src ./src
COPY package.json ./

# Non-root user for security
# See: https://docs.docker.com/reference/dockerfile/#user
USER bun

# OCI image labels for metadata and traceability
# See: https://docs.docker.com/reference/dockerfile/#label
# Spec: https://github.com/opencontainers/image-spec/blob/main/annotations.md
LABEL org.opencontainers.image.title="spec-driven-pipeline"
LABEL com.spec-driven.verified="true"

# Jobs run once and exit - no HEALTHCHECK needed for batch jobs
CMD ["bun", "run", "src/index.ts"]
