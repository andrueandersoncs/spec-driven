#!/bin/bash
# parse-dafny-output.sh - Parse Dafny verification output into structured format
# Usage: dafny verify ... 2>&1 | bash ${CLAUDE_PLUGIN_ROOT}/scripts/parse-dafny-output.sh [--summary|--errors|--full]
#
# Output modes:
#   --summary  : JSON with pass/fail, error/warning counts (default)
#   --errors   : JSON array of errors with file, line, message
#   --full     : Original output passed through (for debugging)
#
# Exit codes:
#   0 - Parsing successful (doesn't indicate verification success)

set -euo pipefail

OUTPUT_MODE="${1:---summary}"

# Read all input
input=$(cat)

# Count different result types
verified_count=$(echo "$input" | grep -c "Dafny program verifier finished with [0-9]* verified" 2>/dev/null || echo "0")
error_count=$(echo "$input" | grep -cE "^[^:]+\.dfy\([0-9]+,[0-9]+\): Error" 2>/dev/null || echo "0")
warning_count=$(echo "$input" | grep -cE "^[^:]+\.dfy\([0-9]+,[0-9]+\): Warning" 2>/dev/null || echo "0")

# Extract verified count from summary line
methods_verified=$(echo "$input" | grep -oE "[0-9]+ verified" | grep -oE "[0-9]+" | head -1 || echo "0")
methods_verified="${methods_verified:-0}"

# Determine overall status
if echo "$input" | grep -q "0 errors"; then
  status="passed"
elif [ "$error_count" -gt 0 ]; then
  status="failed"
elif echo "$input" | grep -q "Error:"; then
  status="failed"
  error_count=$(echo "$input" | grep -c "Error:" 2>/dev/null || echo "1")
else
  status="passed"
fi

case "$OUTPUT_MODE" in
  --summary)
    # Categorize errors by type
    precondition_errors=$(echo "$input" | grep -c "precondition might not hold" 2>/dev/null || echo "0")
    postcondition_errors=$(echo "$input" | grep -c "postcondition might not hold" 2>/dev/null || echo "0")
    invariant_errors=$(echo "$input" | grep -c "invariant might not hold\|loop invariant" 2>/dev/null || echo "0")
    assertion_errors=$(echo "$input" | grep -c "assertion might not hold" 2>/dev/null || echo "0")
    decreases_errors=$(echo "$input" | grep -c "decreases\|termination" 2>/dev/null || echo "0")
    syntax_errors=$(echo "$input" | grep -c "unexpected token\|expected\|parse error" 2>/dev/null || echo "0")
    other_errors=$((error_count - precondition_errors - postcondition_errors - invariant_errors - assertion_errors - decreases_errors - syntax_errors))
    [ "$other_errors" -lt 0 ] && other_errors=0

    cat <<EOF
{
  "status": "$status",
  "verified": $methods_verified,
  "errors": $error_count,
  "warnings": $warning_count,
  "by_type": {
    "precondition": $precondition_errors,
    "postcondition": $postcondition_errors,
    "invariant": $invariant_errors,
    "assertion": $assertion_errors,
    "termination": $decreases_errors,
    "syntax": $syntax_errors,
    "other": $other_errors
  }
}
EOF
    ;;

  --errors)
    # Extract structured error information
    echo "["
    first=true

    # Parse error lines: file.dfy(line,col): Error: message
    echo "$input" | grep -E "^[^:]+\.dfy\([0-9]+,[0-9]+\): Error" | while read -r line; do
      # Extract components
      file=$(echo "$line" | sed -E 's/^([^(]+)\.dfy\(.*/\1.dfy/')
      location=$(echo "$line" | sed -E 's/^[^(]+\.dfy\(([0-9]+),([0-9]+)\).*/\1:\2/')
      line_num=$(echo "$location" | cut -d: -f1)
      col_num=$(echo "$location" | cut -d: -f2)
      message=$(echo "$line" | sed -E 's/^[^:]+\.dfy\([0-9]+,[0-9]+\): Error: //')

      # Determine error type
      if echo "$message" | grep -q "precondition"; then
        error_type="precondition"
      elif echo "$message" | grep -q "postcondition"; then
        error_type="postcondition"
      elif echo "$message" | grep -q "invariant"; then
        error_type="invariant"
      elif echo "$message" | grep -q "assertion"; then
        error_type="assertion"
      elif echo "$message" | grep -q "decreases\|termination"; then
        error_type="termination"
      else
        error_type="other"
      fi

      if [ "$first" = true ]; then
        first=false
      else
        echo ","
      fi

      # Escape message for JSON
      escaped_message=$(echo "$message" | sed 's/\\/\\\\/g; s/"/\\"/g' | tr '\n' ' ')

      cat <<ERRJSON
  {
    "file": "$file",
    "line": $line_num,
    "column": $col_num,
    "type": "$error_type",
    "message": "$escaped_message"
  }
ERRJSON
    done
    echo ""
    echo "]"
    ;;

  --full)
    echo "$input"
    ;;

  *)
    echo "Unknown mode: $OUTPUT_MODE" >&2
    echo "Usage: ... | parse-dafny-output.sh [--summary|--errors|--full]" >&2
    exit 1
    ;;
esac
