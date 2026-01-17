#!/bin/bash
# check-tools.sh - Verify required tools for spec-driven development are installed
# Usage: bash ${CLAUDE_PLUGIN_ROOT}/scripts/check-tools.sh
#
# Exit codes:
#   0 - All required tools available
#   1 - One or more required tools missing

set -euo pipefail

# Colors for output (if terminal supports them)
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m' # No Color

# Track missing tools
missing_required=0
missing_optional=0

echo "Checking spec-driven development tools..."
echo ""

# ==========================================
# Required Tools
# ==========================================

echo "Required tools:"

# Check Dafny
if command -v dafny &> /dev/null; then
  version=$(dafny --version 2>/dev/null | head -1 || echo "unknown version")
  echo -e "  ${GREEN}✓${NC} dafny: $version"
else
  echo -e "  ${RED}✗${NC} dafny: NOT FOUND"
  echo "    Install: brew install dafny (macOS) or see https://dafny.org/latest/Installation"
  missing_required=1
fi

# Check TLC (Java + tla2tools.jar)
if command -v java &> /dev/null; then
  java_version=$(java -version 2>&1 | head -1)
  echo -e "  ${GREEN}✓${NC} java: $java_version"

  # Check for TLA+ tools
  if [ -n "${TLA2TOOLS_JAR:-}" ] && [ -f "$TLA2TOOLS_JAR" ]; then
    echo -e "  ${GREEN}✓${NC} tlc: available via \$TLA2TOOLS_JAR"
  elif command -v tlc &> /dev/null; then
    echo -e "  ${GREEN}✓${NC} tlc: available"
  else
    # Try common locations
    found_tlc=0
    for jar in /usr/local/share/java/tla2tools.jar /opt/homebrew/share/java/tla2tools.jar ~/tla2tools.jar; do
      if [ -f "$jar" ]; then
        echo -e "  ${GREEN}✓${NC} tlc: found at $jar"
        echo "    Tip: export TLA2TOOLS_JAR=$jar"
        found_tlc=1
        break
      fi
    done
    if [ $found_tlc -eq 0 ]; then
      echo -e "  ${RED}✗${NC} tlc: NOT FOUND"
      echo "    Install: brew install tlaplus (macOS) or download from https://github.com/tlaplus/tlaplus/releases"
      missing_required=1
    fi
  fi
else
  echo -e "  ${RED}✗${NC} java: NOT FOUND (required for TLC)"
  echo "    Install: brew install openjdk (macOS) or install JDK 11+"
  missing_required=1
fi

# Check Bun
if command -v bun &> /dev/null; then
  version=$(bun --version 2>/dev/null || echo "unknown")
  echo -e "  ${GREEN}✓${NC} bun: $version"
else
  echo -e "  ${RED}✗${NC} bun: NOT FOUND"
  echo "    Install: curl -fsSL https://bun.sh/install | bash"
  missing_required=1
fi

echo ""

# ==========================================
# Optional Tools
# ==========================================

echo "Optional tools:"

# Check jq
if command -v jq &> /dev/null; then
  version=$(jq --version 2>/dev/null || echo "unknown")
  echo -e "  ${GREEN}✓${NC} jq: $version (JSON processing)"
else
  echo -e "  ${YELLOW}○${NC} jq: not found (recommended for JSON processing)"
  missing_optional=1
fi

# Check Docker
if command -v docker &> /dev/null; then
  version=$(docker --version 2>/dev/null | head -1 || echo "unknown")
  echo -e "  ${GREEN}✓${NC} docker: $version (for /deploy command)"
else
  echo -e "  ${YELLOW}○${NC} docker: not found (needed for /deploy command)"
  missing_optional=1
fi

# Check GraphViz (for TLA+ state graphs)
if command -v dot &> /dev/null; then
  version=$(dot -V 2>&1 | head -1 || echo "unknown")
  echo -e "  ${GREEN}✓${NC} graphviz: $version (TLA+ state graph visualization)"
else
  echo -e "  ${YELLOW}○${NC} graphviz: not found (optional for TLA+ state graph visualization)"
  missing_optional=1
fi

# Check TypeScript
if command -v tsc &> /dev/null; then
  version=$(tsc --version 2>/dev/null || echo "unknown")
  echo -e "  ${GREEN}✓${NC} typescript: $version (type checking)"
else
  echo -e "  ${YELLOW}○${NC} typescript: not found (Bun handles TS natively, but tsc useful for checking)"
  missing_optional=1
fi

echo ""

# ==========================================
# Summary
# ==========================================

if [ $missing_required -eq 0 ]; then
  echo -e "${GREEN}All required tools are available!${NC}"
  if [ $missing_optional -gt 0 ]; then
    echo -e "${YELLOW}Some optional tools are missing (see above).${NC}"
  fi
  echo ""
  echo "You're ready to use spec-driven development."
  echo "Run /probe-domain to get started with a new project."
  exit 0
else
  echo -e "${RED}Some required tools are missing!${NC}"
  echo ""
  echo "Options:"
  echo "  1. Install missing tools manually (see instructions above)"
  echo "  2. Use Nix: nix develop (if flake.nix exists)"
  echo ""
  echo "For Nix setup, copy the template:"
  echo "  cp \${CLAUDE_PLUGIN_ROOT}/templates/flake.nix ./flake.nix"
  echo "  nix develop"
  exit 1
fi
