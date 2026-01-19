#!/bin/bash
# verify-all.sh - Run all formal verification (Dafny + TLC) with combined summary
# Usage: bash ${CLAUDE_PLUGIN_ROOT}/scripts/verify-all.sh [--summary|--detailed|--full]
#
# Output modes:
#   --summary   : One-line status for each tool + overall result (default)
#   --detailed  : JSON with full breakdown of both tools
#   --full      : Complete output from both tools
#
# Exit codes:
#   0 - All verification passed
#   1 - One or more verifications failed
#   2 - No specs found

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="${CLAUDE_PROJECT_DIR:-$(pwd)}"

OUTPUT_MODE="${1:---summary}"

# Check for specs directory
if [ ! -d "$PROJECT_DIR/specs" ]; then
  echo '{"status": "error", "message": "No specs/ directory found. Run /probe-domain to start."}' >&2
  exit 2
fi

# Detect what specs exist
has_dafny=false
has_tla=false

if [ -d "$PROJECT_DIR/specs/dafny" ] && ls "$PROJECT_DIR/specs/dafny"/*.dfy &>/dev/null 2>&1; then
  has_dafny=true
fi

if [ -d "$PROJECT_DIR/specs/tla" ] && [ -f "$PROJECT_DIR/specs/tla/behavior.tla" ]; then
  has_tla=true
fi

if [ "$has_dafny" = false ] && [ "$has_tla" = false ]; then
  echo '{"status": "error", "message": "No Dafny (.dfy) or TLA+ (.tla) specs found in specs/"}' >&2
  exit 2
fi

# Initialize results
dafny_status="skipped"
dafny_result=""
tlc_status="skipped"
tlc_result=""
overall_status="passed"

# Run Dafny verification if specs exist
if [ "$has_dafny" = true ]; then
  if [ "$OUTPUT_MODE" = "--full" ]; then
    echo "===== Dafny Verification ====="
    dafny_result=$(bash "$SCRIPT_DIR/run-dafny-verify.sh" --full 2>&1 || true)
    echo "$dafny_result"
    echo ""
    # Get status
    if echo "$dafny_result" | grep -q "0 errors"; then
      dafny_status="passed"
    else
      dafny_status="failed"
      overall_status="failed"
    fi
  else
    dafny_result=$(bash "$SCRIPT_DIR/run-dafny-verify.sh" --summary 2>&1 || true)
    dafny_status=$(echo "$dafny_result" | grep -o '"status": "[^"]*"' | cut -d'"' -f4 || echo "error")
    if [ "$dafny_status" != "passed" ]; then
      overall_status="failed"
    fi
  fi
fi

# Run TLC model checking if specs exist
if [ "$has_tla" = true ]; then
  if [ "$OUTPUT_MODE" = "--full" ]; then
    echo "===== TLC Model Checking ====="
    tlc_result=$(bash "$SCRIPT_DIR/run-tlc.sh" --full 2>&1 || true)
    echo "$tlc_result"
    echo ""
    # Get status
    if echo "$tlc_result" | grep -q "Model checking completed. No error has been found"; then
      tlc_status="passed"
    else
      tlc_status="failed"
      overall_status="failed"
    fi
  else
    tlc_result=$(bash "$SCRIPT_DIR/run-tlc.sh" --summary 2>&1 || true)
    tlc_status=$(echo "$tlc_result" | grep -o '"status": "[^"]*"' | cut -d'"' -f4 || echo "error")
    if [ "$tlc_status" != "passed" ]; then
      overall_status="failed"
    fi
  fi
fi

# Output based on mode
case "$OUTPUT_MODE" in
  --summary)
    echo "Verification Summary"
    echo "===================="

    if [ "$has_dafny" = true ]; then
      if [ "$dafny_status" = "passed" ]; then
        verified=$(echo "$dafny_result" | grep -o '"verified": [0-9]*' | cut -d' ' -f2 || echo "?")
        echo "Dafny (Structure): PASSED ($verified methods verified)"
      else
        errors=$(echo "$dafny_result" | grep -o '"errors": [0-9]*' | cut -d' ' -f2 || echo "?")
        echo "Dafny (Structure): FAILED ($errors errors)"
      fi
    else
      echo "Dafny (Structure): SKIPPED (no .dfy files)"
    fi

    if [ "$has_tla" = true ]; then
      if [ "$tlc_status" = "passed" ]; then
        states=$(echo "$tlc_result" | grep -o '"distinct": [0-9]*' | cut -d' ' -f2 || echo "?")
        echo "TLC (Behavior):    PASSED ($states distinct states)"
      else
        violation=$(echo "$tlc_result" | grep -o '"violation_type": "[^"]*"' | cut -d'"' -f4 || echo "unknown")
        echo "TLC (Behavior):    FAILED ($violation)"
      fi
    else
      echo "TLC (Behavior):    SKIPPED (no .tla files)"
    fi

    echo ""
    if [ "$overall_status" = "passed" ]; then
      echo "Overall: ALL PASSED - Ready for /generate"
    else
      echo "Overall: FAILED - Fix issues and re-run /verify"
    fi
    ;;

  --detailed)
    # Build JSON output
    cat <<EOF
{
  "overall": "$overall_status",
  "dafny": {
    "status": "$dafny_status",
    "result": $dafny_result
  },
  "tlc": {
    "status": "$tlc_status",
    "result": $tlc_result
  }
}
EOF
    ;;

  --full)
    echo "===== Overall Result ====="
    if [ "$overall_status" = "passed" ]; then
      echo "ALL VERIFICATION PASSED"
    else
      echo "VERIFICATION FAILED"
    fi
    ;;
esac

# Exit with appropriate code
if [ "$overall_status" = "passed" ]; then
  exit 0
else
  exit 1
fi
