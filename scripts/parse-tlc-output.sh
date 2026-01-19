#!/bin/bash
# parse-tlc-output.sh - Parse TLC model checker output into structured format
# Usage: tlc ... 2>&1 | bash ${CLAUDE_PLUGIN_ROOT}/scripts/parse-tlc-output.sh [--summary|--trace|--trace-full|--violated]
#
# Output modes:
#   --summary     : JSON with states explored, violations, status (default)
#   --trace       : Abbreviated counterexample trace (first 5 states + last)
#   --trace-full  : Complete counterexample trace
#   --violated    : JSON array of violated properties
#
# Exit codes:
#   0 - Parsing successful (doesn't indicate model checking success)

set -euo pipefail

OUTPUT_MODE="${1:---summary}"

# Read all input
input=$(cat)

# Extract key metrics
states_generated=$(echo "$input" | grep -oE "[0-9]+ states generated" | grep -oE "^[0-9]+" | head -1 || echo "0")
states_distinct=$(echo "$input" | grep -oE "[0-9]+ distinct states" | grep -oE "^[0-9]+" | head -1 || echo "0")
states_left=$(echo "$input" | grep -oE "[0-9]+ states left on queue" | grep -oE "^[0-9]+" | head -1 || echo "0")

# Default values if not found
states_generated="${states_generated:-0}"
states_distinct="${states_distinct:-0}"
states_left="${states_left:-0}"

# Determine status
if echo "$input" | grep -q "Model checking completed. No error has been found"; then
  status="passed"
  violation_type="none"
elif echo "$input" | grep -q "Invariant .* is violated"; then
  status="failed"
  violation_type="invariant"
elif echo "$input" | grep -q "Temporal properties were violated"; then
  status="failed"
  violation_type="temporal"
elif echo "$input" | grep -q "deadlock"; then
  status="failed"
  violation_type="deadlock"
elif echo "$input" | grep -q "Error:"; then
  status="error"
  violation_type="error"
else
  # Check for other success indicators
  if echo "$input" | grep -q "states generated"; then
    status="passed"
    violation_type="none"
  else
    status="unknown"
    violation_type="unknown"
  fi
fi

# Extract violated property names
violated_props=$(echo "$input" | grep -oE "Invariant [A-Za-z_][A-Za-z0-9_]* is violated" | sed 's/Invariant //; s/ is violated//' || true)
violated_temporal=$(echo "$input" | grep -oE "property [A-Za-z_][A-Za-z0-9_]* .* violated" | sed 's/property //; s/ .* violated//' || true)

case "$OUTPUT_MODE" in
  --summary)
    # Count violations
    invariant_violations=$(echo "$input" | grep -c "Invariant .* is violated" 2>/dev/null || echo "0")
    temporal_violations=$(echo "$input" | grep -c "Temporal properties were violated\|property .* violated" 2>/dev/null || echo "0")
    deadlocks=$(echo "$input" | grep -c "deadlock" 2>/dev/null || echo "0")

    # Get trace depth if there's a violation
    trace_depth=$(echo "$input" | grep -c "^State [0-9]*:" 2>/dev/null || echo "0")

    cat <<EOF
{
  "status": "$status",
  "violation_type": "$violation_type",
  "states": {
    "generated": $states_generated,
    "distinct": $states_distinct,
    "queue": $states_left
  },
  "violations": {
    "invariant": $invariant_violations,
    "temporal": $temporal_violations,
    "deadlock": $deadlocks
  },
  "trace_depth": $trace_depth
}
EOF
    ;;

  --trace)
    # Extract abbreviated trace (first 5 states + last if more)
    echo "{"
    echo '  "trace": ['

    # Get all state blocks
    state_count=$(echo "$input" | grep -c "^State [0-9]*:" 2>/dev/null || echo "0")

    if [ "$state_count" -eq 0 ]; then
      echo '  ],'
      echo '  "message": "No counterexample trace found"'
      echo "}"
      exit 0
    fi

    current=0
    in_state=false
    state_content=""

    echo "$input" | while IFS= read -r line; do
      if echo "$line" | grep -qE "^State [0-9]*:"; then
        # Output previous state if we have one
        if [ -n "$state_content" ] && { [ "$current" -le 5 ] || [ "$current" -eq "$state_count" ]; }; then
          if [ "$current" -gt 1 ]; then
            echo ","
          fi
          # Escape and output
          escaped=$(echo "$state_content" | sed 's/\\/\\\\/g; s/"/\\"/g' | tr '\n' ' ' | sed 's/  */ /g')
          echo "    {\"state\": $current, \"content\": \"$escaped\"}"
        fi

        current=$((current + 1))
        state_content="$line"

        # Add ellipsis marker after state 5 if there are more states
        if [ "$current" -eq 6 ] && [ "$state_count" -gt 6 ]; then
          echo ","
          echo "    {\"state\": \"...\", \"content\": \"($((state_count - 6)) states omitted)\"}"
        fi
      else
        state_content="$state_content $line"
      fi
    done

    # Handle last state
    if [ -n "$state_content" ] && [ "$current" -le 5 -o "$current" -eq "$state_count" ]; then
      if [ "$current" -gt 1 ]; then
        echo ","
      fi
      escaped=$(echo "$state_content" | sed 's/\\/\\\\/g; s/"/\\"/g' | tr '\n' ' ' | sed 's/  */ /g')
      echo "    {\"state\": $current, \"content\": \"$escaped\"}"
    fi

    echo ""
    echo "  ],"
    echo "  \"total_states\": $state_count"
    echo "}"
    ;;

  --trace-full)
    # Full trace extraction
    echo "{"
    echo '  "trace": ['

    # Extract everything between "Error:" and the statistics
    in_trace=false
    first=true

    echo "$input" | while IFS= read -r line; do
      if echo "$line" | grep -qE "^State [0-9]*:"; then
        if [ "$first" = false ]; then
          echo ","
        fi
        first=false
        escaped=$(echo "$line" | sed 's/\\/\\\\/g; s/"/\\"/g')
        echo -n "    \"$escaped"
      elif echo "$line" | grep -qE "^/\\\\|^\\\\/|^[a-z_]+ ="; then
        # Continuation of state
        escaped=$(echo "$line" | sed 's/\\/\\\\/g; s/"/\\"/g')
        echo -n " $escaped"
      elif [ "$first" = false ]; then
        echo "\""
      fi
    done

    echo ""
    echo "  ]"
    echo "}"
    ;;

  --violated)
    echo "["
    first=true

    # Invariant violations
    echo "$input" | grep -oE "Invariant [A-Za-z_][A-Za-z0-9_]* is violated" | while read -r line; do
      prop=$(echo "$line" | sed 's/Invariant //; s/ is violated//')
      if [ "$first" = false ]; then
        echo ","
      fi
      first=false
      echo "  {\"type\": \"invariant\", \"name\": \"$prop\"}"
    done

    # Temporal violations
    echo "$input" | grep -oE "property [A-Za-z_][A-Za-z0-9_]*" | while read -r line; do
      prop=$(echo "$line" | sed 's/property //')
      if [ "$first" = false ]; then
        echo ","
      fi
      first=false
      echo "  {\"type\": \"temporal\", \"name\": \"$prop\"}"
    done

    # Deadlock
    if echo "$input" | grep -q "deadlock"; then
      if [ "$first" = false ]; then
        echo ","
      fi
      echo "  {\"type\": \"deadlock\", \"name\": \"deadlock\"}"
    fi

    echo ""
    echo "]"
    ;;

  *)
    echo "Unknown mode: $OUTPUT_MODE" >&2
    echo "Usage: ... | parse-tlc-output.sh [--summary|--trace|--trace-full|--violated]" >&2
    exit 1
    ;;
esac
