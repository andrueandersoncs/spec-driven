# syntax=docker/dockerfile:1
# Enables BuildKit features. See: https://docs.docker.com/build/buildkit/
#
# @generated from specs
# Web service Dockerfile for spec-driven Bun applications
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
RUN bun install --frozen-lockfile --production=false

# Copy source and build
COPY src/ ./src/
COPY tsconfig.json ./
RUN bun build src/index.ts --outdir dist --target bun --minify

# Production stage - use slim image to reduce attack surface
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

# OCI image labels for metadata and traceability
# See: https://docs.docker.com/reference/dockerfile/#label
# Spec: https://github.com/opencontainers/image-spec/blob/main/annotations.md
LABEL org.opencontainers.image.title="spec-driven-web-service"
LABEL com.spec-driven.verified="true"

EXPOSE 3000
CMD ["bun", "run", "dist/index.js"]
