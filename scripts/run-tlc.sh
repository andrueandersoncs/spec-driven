#!/bin/bash
# run-tlc.sh - Run TLC model checker with standardized output handling
# Usage: bash ${CLAUDE_PLUGIN_ROOT}/scripts/run-tlc.sh [--summary|--trace|--trace-full|--violated|--full] [spec.tla] [config.cfg]
#
# Arguments:
#   --summary     : Show JSON summary of model checking results (default)
#   --trace       : Show abbreviated counterexample trace (first 5 + last state)
#   --trace-full  : Show complete counterexample trace
#   --violated    : Show JSON array of violated properties
#   --full        : Show complete TLC output
#   spec.tla      : TLA+ spec file (default: specs/tla/behavior.tla)
#   config.cfg    : TLC config file (default: specs/tla/behavior.cfg)
#
# Exit codes:
#   0 - Model checking passed (no violations)
#   1 - Model checking failed (violations found)
#   2 - Spec or config file not found
#   3 - Nix not available

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="${CLAUDE_PROJECT_DIR:-$(pwd)}"

# Parse arguments
OUTPUT_MODE="--summary"
SPEC_FILE=""
CONFIG_FILE=""

for arg in "$@"; do
  case "$arg" in
    --summary|--trace|--trace-full|--violated|--full)
      OUTPUT_MODE="$arg"
      ;;
    *.tla)
      SPEC_FILE="$arg"
      ;;
    *.cfg)
      CONFIG_FILE="$arg"
      ;;
  esac
done

# Default paths
if [ -z "$SPEC_FILE" ]; then
  SPEC_FILE="$PROJECT_DIR/specs/tla/behavior.tla"
fi
if [ -z "$CONFIG_FILE" ]; then
  # Derive config from spec file
  CONFIG_FILE="${SPEC_FILE%.tla}.cfg"
fi

# Make paths absolute if relative
if [[ ! "$SPEC_FILE" = /* ]]; then
  SPEC_FILE="$PROJECT_DIR/$SPEC_FILE"
fi
if [[ ! "$CONFIG_FILE" = /* ]]; then
  CONFIG_FILE="$PROJECT_DIR/$CONFIG_FILE"
fi

# Check Nix availability
if ! command -v nix-shell &> /dev/null; then
  echo '{"status": "error", "message": "Nix is required but not installed. Install with: curl -L https://nixos.org/nix/install | sh"}' >&2
  exit 3
fi

# Check spec file exists
if [ ! -f "$SPEC_FILE" ]; then
  echo '{"status": "error", "message": "TLA+ spec not found: '"$SPEC_FILE"'"}' >&2
  exit 2
fi

# Check config file exists
if [ ! -f "$CONFIG_FILE" ]; then
  echo '{"status": "error", "message": "TLC config not found: '"$CONFIG_FILE"'. Create one or specify with: run-tlc.sh spec.tla config.cfg"}' >&2
  exit 2
fi

# Change to spec directory for TLC (it expects relative paths in config)
SPEC_DIR=$(dirname "$SPEC_FILE")
SPEC_NAME=$(basename "$SPEC_FILE")
CONFIG_NAME=$(basename "$CONFIG_FILE")

# Run TLC
raw_output=$(cd "$SPEC_DIR" && nix-shell -p tlaplus --run "tlc $SPEC_NAME -config $CONFIG_NAME -workers auto" 2>&1 || true)

# Handle --full mode separately (don't parse)
if [ "$OUTPUT_MODE" = "--full" ]; then
  echo "$raw_output"
  # Still need to determine exit code
  if echo "$raw_output" | grep -q "Model checking completed. No error has been found"; then
    exit 0
  else
    exit 1
  fi
fi

# Parse output based on mode
result=$(echo "$raw_output" | bash "$SCRIPT_DIR/parse-tlc-output.sh" "$OUTPUT_MODE")
echo "$result"

# Determine exit code from summary
status=$(echo "$raw_output" | bash "$SCRIPT_DIR/parse-tlc-output.sh" --summary | grep -o '"status": "[^"]*"' | cut -d'"' -f4)
if [ "$status" = "passed" ]; then
  exit 0
else
  exit 1
fi
