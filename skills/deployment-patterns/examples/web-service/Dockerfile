# syntax=docker/dockerfile:1
# @generated from specs
# Web service Dockerfile for spec-driven Bun applications

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

# Health check - derived from spec assertions
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
  CMD bun run dist/health.js || exit 1

# Verification metadata for traceability
LABEL org.opencontainers.image.title="spec-driven-web-service"
LABEL com.spec-driven.verified="true"

EXPOSE 3000
CMD ["bun", "run", "dist/index.js"]
