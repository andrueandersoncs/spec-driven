#!/bin/bash
# Load specification context at session start
# This script checks for existing specs and provides context to Claude

set -euo pipefail

PROJECT_DIR="${CLAUDE_PROJECT_DIR:-$(pwd)}"

# Initialize output
output=""

# Check if specs directory exists
if [ -d "$PROJECT_DIR/specs" ]; then
  output="Spec-driven project detected."

  # Check for assertions manifest
  if [ -f "$PROJECT_DIR/specs/assertions.json" ]; then
    # Count assertions by status
    total=$(jq '.assertions | length' "$PROJECT_DIR/specs/assertions.json" 2>/dev/null || echo "0")
    confirmed=$(jq '[.assertions[] | select(.status == "confirmed")] | length' "$PROJECT_DIR/specs/assertions.json" 2>/dev/null || echo "0")
    pending=$(jq '[.assertions[] | select(.status == "pending")] | length' "$PROJECT_DIR/specs/assertions.json" 2>/dev/null || echo "0")

    output="$output Assertions: $total total ($confirmed confirmed, $pending pending)."

    # Get archetype and domains
    archetype=$(jq -r '.archetype // "unknown"' "$PROJECT_DIR/specs/assertions.json" 2>/dev/null)
    domains=$(jq -r '.domains // [] | join(", ")' "$PROJECT_DIR/specs/assertions.json" 2>/dev/null)

    if [ "$archetype" != "unknown" ] && [ "$archetype" != "null" ]; then
      output="$output Archetype: $archetype."
    fi
    if [ -n "$domains" ] && [ "$domains" != "null" ]; then
      output="$output Domains: $domains."
    fi
  fi

  # Check for Dafny specs
  dafny_count=$(find "$PROJECT_DIR/specs/dafny" -name "*.dfy" 2>/dev/null | wc -l | tr -d ' ')
  if [ "$dafny_count" -gt 0 ]; then
    output="$output Dafny specs: $dafny_count files."
  fi

  # Check for TLA+ specs
  tla_count=$(find "$PROJECT_DIR/specs/tla" -name "*.tla" 2>/dev/null | wc -l | tr -d ' ')
  if [ "$tla_count" -gt 0 ]; then
    output="$output TLA+ specs: $tla_count files."
  fi

  # Provide guidance
  if [ "$pending" -gt 0 ] 2>/dev/null; then
    output="$output Run /interview to confirm pending assertions."
  elif [ "$dafny_count" -gt 0 ] || [ "$tla_count" -gt 0 ]; then
    output="$output Use /verify to check specs, /generate to create code."
  fi
else
  # No specs directory - might be a new project
  output="No specs/ directory found. Use /probe-domain to start spec-driven development."
fi

# Output context message
if [ -n "$output" ]; then
  echo "{\"systemMessage\": \"$output\"}"
fi
