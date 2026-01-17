#!/bin/bash
# Check if running tests without package.json
# Only warns for test commands; approves all other commands silently

set -euo pipefail

# Read JSON input from stdin
input=$(cat)

# Extract the bash command from tool_input
COMMAND=$(echo "$input" | jq -r '.tool_input.command // ""')

# Check if this is a test command
if [[ "$COMMAND" =~ (bun|npm|yarn|pnpm)[[:space:]]+(test|run[[:space:]]+test) ]]; then
    # It's a test command - check if package.json exists
    if [[ ! -f "package.json" ]]; then
        echo "Warning: Cannot run tests without package.json. Run /scaffold first to set up the project." >&2
        exit 2
    fi
fi

# All other commands (or test commands with package.json) are approved
exit 0
