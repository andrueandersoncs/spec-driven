# syntax=docker/dockerfile:1
# @generated from specs
# Data pipeline Dockerfile - for batch/stream processing jobs

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

# Non-root user for security
USER bun

# Verification metadata
LABEL org.opencontainers.image.title="spec-driven-pipeline"
LABEL com.spec-driven.verified="true"

# Jobs run once and exit
CMD ["bun", "run", "src/index.ts"]
