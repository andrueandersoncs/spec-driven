#!/bin/bash
# validate-assertions.sh - Validate assertions.json schema and content
# Usage: bash ${CLAUDE_PLUGIN_ROOT}/scripts/validate-assertions.sh [path/to/assertions.json]
#
# If no path provided, defaults to specs/assertions.json
#
# Exit codes:
#   0 - Valid assertions.json
#   1 - File not found or invalid JSON
#   2 - Schema validation errors

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

# Get file path
ASSERTIONS_FILE="${1:-specs/assertions.json}"

echo "Validating: $ASSERTIONS_FILE"
echo ""

# ==========================================
# Check file exists
# ==========================================

if [ ! -f "$ASSERTIONS_FILE" ]; then
  echo -e "${RED}Error: File not found: $ASSERTIONS_FILE${NC}"
  exit 1
fi

# ==========================================
# Check valid JSON
# ==========================================

if ! jq empty "$ASSERTIONS_FILE" 2>/dev/null; then
  echo -e "${RED}Error: Invalid JSON syntax${NC}"
  jq . "$ASSERTIONS_FILE" 2>&1 | head -5
  exit 1
fi

echo -e "${GREEN}✓${NC} Valid JSON syntax"

# ==========================================
# Check required fields
# ==========================================

errors=0

# Check version
version=$(jq -r '.version // empty' "$ASSERTIONS_FILE")
if [ -z "$version" ]; then
  echo -e "${RED}✗${NC} Missing required field: version"
  errors=1
else
  echo -e "${GREEN}✓${NC} version: $version"
fi

# Check assertions array
if ! jq -e '.assertions' "$ASSERTIONS_FILE" >/dev/null 2>&1; then
  echo -e "${RED}✗${NC} Missing required field: assertions (array)"
  errors=1
else
  count=$(jq '.assertions | length' "$ASSERTIONS_FILE")
  echo -e "${GREEN}✓${NC} assertions: $count entries"
fi

# ==========================================
# Validate each assertion
# ==========================================

echo ""
echo "Validating assertion entries..."

assertion_errors=0
jq -c '.assertions[]?' "$ASSERTIONS_FILE" 2>/dev/null | while read -r assertion; do
  id=$(echo "$assertion" | jq -r '.id // "MISSING_ID"')

  # Check required fields
  missing_fields=()

  [ "$(echo "$assertion" | jq -r '.id // empty')" = "" ] && missing_fields+=("id")
  [ "$(echo "$assertion" | jq -r '.natural // empty')" = "" ] && missing_fields+=("natural")
  [ "$(echo "$assertion" | jq -r '.type // empty')" = "" ] && missing_fields+=("type")
  [ "$(echo "$assertion" | jq -r '.category // empty')" = "" ] && missing_fields+=("category")
  [ "$(echo "$assertion" | jq -r '.status // empty')" = "" ] && missing_fields+=("status")

  if [ ${#missing_fields[@]} -gt 0 ]; then
    echo -e "  ${RED}✗${NC} [$id] Missing fields: ${missing_fields[*]}"
    assertion_errors=1
    continue
  fi

  # Validate type
  type=$(echo "$assertion" | jq -r '.type')
  valid_types="invariant precondition postcondition safety liveness ordering fairness reachability data-constraint relationship uniqueness"
  if ! echo "$valid_types" | grep -qw "$type"; then
    echo -e "  ${YELLOW}!${NC} [$id] Unknown type: $type"
  fi

  # Validate category
  category=$(echo "$assertion" | jq -r '.category')
  if [ "$category" != "structure" ] && [ "$category" != "behavior" ]; then
    echo -e "  ${RED}✗${NC} [$id] Invalid category: $category (must be 'structure' or 'behavior')"
    assertion_errors=1
    continue
  fi

  # Validate status
  status=$(echo "$assertion" | jq -r '.status')
  valid_statuses="proposed pending confirmed denied"
  if ! echo "$valid_statuses" | grep -qw "$status"; then
    echo -e "  ${RED}✗${NC} [$id] Invalid status: $status"
    assertion_errors=1
    continue
  fi

  # Valid assertion
  natural=$(echo "$assertion" | jq -r '.natural' | head -c 50)
  echo -e "  ${GREEN}✓${NC} [$id] ($category/$type) $natural..."
done

# ==========================================
# Check for duplicates
# ==========================================

echo ""
echo "Checking for duplicates..."

duplicate_ids=$(jq -r '.assertions[].id' "$ASSERTIONS_FILE" 2>/dev/null | sort | uniq -d)
if [ -n "$duplicate_ids" ]; then
  echo -e "${RED}✗${NC} Duplicate assertion IDs found:"
  echo "$duplicate_ids" | while read -r id; do
    echo "    - $id"
  done
  errors=1
else
  echo -e "${GREEN}✓${NC} No duplicate IDs"
fi

# ==========================================
# Summary
# ==========================================

echo ""

# Count by status
confirmed=$(jq '[.assertions[] | select(.status == "confirmed")] | length' "$ASSERTIONS_FILE")
pending=$(jq '[.assertions[] | select(.status == "pending")] | length' "$ASSERTIONS_FILE")
proposed=$(jq '[.assertions[] | select(.status == "proposed")] | length' "$ASSERTIONS_FILE")
denied=$(jq '[.assertions[] | select(.status == "denied")] | length' "$ASSERTIONS_FILE")

echo "Summary:"
echo "  Total assertions: $(jq '.assertions | length' "$ASSERTIONS_FILE")"
echo "  - Confirmed: $confirmed"
echo "  - Pending: $pending"
echo "  - Proposed: $proposed"
echo "  - Denied: $denied"

# Count by category
structure=$(jq '[.assertions[] | select(.category == "structure")] | length' "$ASSERTIONS_FILE")
behavior=$(jq '[.assertions[] | select(.category == "behavior")] | length' "$ASSERTIONS_FILE")
echo "  By category:"
echo "  - Structure (Dafny): $structure"
echo "  - Behavior (TLA+): $behavior"

echo ""

if [ $errors -eq 0 ] && [ $assertion_errors -eq 0 ]; then
  echo -e "${GREEN}Validation passed!${NC}"
  exit 0
else
  echo -e "${RED}Validation failed with errors.${NC}"
  exit 2
fi
