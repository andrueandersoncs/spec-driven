#!/bin/bash
# run-dafny-verify.sh - Run Dafny verification with standardized output handling
# Usage: bash ${CLAUDE_PLUGIN_ROOT}/scripts/run-dafny-verify.sh [--summary|--errors|--full] [path/to/specs]
#
# Arguments:
#   --summary  : Show JSON summary of verification results (default)
#   --errors   : Show JSON array of errors with locations
#   --full     : Show complete Dafny output
#   path       : Path to .dfy files (default: specs/dafny/*.dfy)
#
# Exit codes:
#   0 - Verification passed
#   1 - Verification failed
#   2 - No .dfy files found
#   3 - Nix not available

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="${CLAUDE_PROJECT_DIR:-$(pwd)}"

# Parse arguments
OUTPUT_MODE="--summary"
SPECS_PATH=""

for arg in "$@"; do
  case "$arg" in
    --summary|--errors|--full)
      OUTPUT_MODE="$arg"
      ;;
    *)
      SPECS_PATH="$arg"
      ;;
  esac
done

# Default specs path
if [ -z "$SPECS_PATH" ]; then
  SPECS_PATH="$PROJECT_DIR/specs/dafny"
fi

# Check Nix availability
if ! command -v nix-shell &> /dev/null; then
  echo '{"status": "error", "message": "Nix is required but not installed. Install with: curl -L https://nixos.org/nix/install | sh"}' >&2
  exit 3
fi

# Check for .dfy files
if [ -d "$SPECS_PATH" ]; then
  dfy_files=$(find "$SPECS_PATH" -name "*.dfy" 2>/dev/null | head -1)
  if [ -z "$dfy_files" ]; then
    echo '{"status": "error", "message": "No .dfy files found in '"$SPECS_PATH"'"}' >&2
    exit 2
  fi
  VERIFY_TARGET="$SPECS_PATH/*.dfy"
elif [ -f "$SPECS_PATH" ]; then
  VERIFY_TARGET="$SPECS_PATH"
else
  echo '{"status": "error", "message": "Path not found: '"$SPECS_PATH"'"}' >&2
  exit 2
fi

# Run Dafny verification
raw_output=$(nix-shell -p dafny --run "dafny verify $VERIFY_TARGET" 2>&1 || true)

# Parse output based on mode
result=$(echo "$raw_output" | bash "$SCRIPT_DIR/parse-dafny-output.sh" "$OUTPUT_MODE")
echo "$result"

# Determine exit code from summary
if [ "$OUTPUT_MODE" = "--summary" ] || [ "$OUTPUT_MODE" = "--errors" ]; then
  # Get status for exit code
  status=$(echo "$raw_output" | bash "$SCRIPT_DIR/parse-dafny-output.sh" --summary | grep -o '"status": "[^"]*"' | cut -d'"' -f4)
  if [ "$status" = "passed" ]; then
    exit 0
  else
    exit 1
  fi
fi
