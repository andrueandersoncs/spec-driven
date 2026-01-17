#!/bin/bash
# Check if running tests without package.json
# Only warns for test commands; approves all other commands silently

COMMAND="$CLAUDE_BASH_COMMAND"

# Check if this is a test command
if [[ "$COMMAND" =~ (bun|npm|yarn|pnpm)[[:space:]]+(test|run[[:space:]]+test) ]]; then
    # It's a test command - check if package.json exists
    if [[ ! -f "package.json" ]]; then
        echo "Warning: Cannot run tests without package.json. Run /scaffold first to set up the project."
        exit 1
    fi
fi

# All other commands (or test commands with package.json) are approved
exit 0
