#!/bin/bash
# check-tools.sh - Verify Nix and required tools for spec-driven development
# Usage: bash ${CLAUDE_PLUGIN_ROOT}/scripts/check-tools.sh
#
# Exit codes:
#   0 - All required tools available (via Nix)
#   1 - Nix not available

set -euo pipefail

# Colors for output (if terminal supports them)
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

echo "Checking spec-driven development environment..."
echo ""

# ==========================================
# Check Nix
# ==========================================

echo "Nix (required):"

if command -v nix-shell &> /dev/null; then
  nix_version=$(nix --version 2>/dev/null || echo "unknown version")
  echo -e "  ${GREEN}✓${NC} nix: $nix_version"
  echo ""

  # ==========================================
  # Verify tools are available via Nix
  # ==========================================

  echo "Verifying tools via Nix (this may take a moment on first run)..."
  echo ""

  # Check Dafny
  echo -n "  Dafny: "
  if dafny_version=$(nix-shell -p dafny --run "dafny --version 2>/dev/null | head -1" 2>/dev/null); then
    echo -e "${GREEN}✓${NC} $dafny_version"
  else
    echo -e "${RED}✗${NC} failed to load via nix-shell"
  fi

  # Check TLA+/TLC
  echo -n "  TLC:   "
  if tlc_version=$(nix-shell -p tlaplus --run "tlc -h 2>&1 | grep -m1 Version || echo 'available'" 2>/dev/null); then
    echo -e "${GREEN}✓${NC} $tlc_version"
  else
    echo -e "${RED}✗${NC} failed to load via nix-shell"
  fi

  # Check Bun
  echo -n "  Bun:   "
  if bun_version=$(nix-shell -p bun --run "bun --version" 2>/dev/null); then
    echo -e "${GREEN}✓${NC} $bun_version"
  else
    echo -e "${RED}✗${NC} failed to load via nix-shell"
  fi

  echo ""

  # ==========================================
  # Optional: Check for flake.nix
  # ==========================================

  echo "Project setup:"
  if [ -f "flake.nix" ]; then
    echo -e "  ${GREEN}✓${NC} flake.nix found - run 'nix develop' for full dev shell"
  else
    echo -e "  ${YELLOW}○${NC} No flake.nix - tools run via nix-shell -p"
    echo "    Copy the template for a persistent dev shell:"
    echo "      cp \${CLAUDE_PLUGIN_ROOT}/templates/flake.nix ./flake.nix"
  fi

  echo ""
  echo -e "${GREEN}All tools available via Nix!${NC}"
  echo ""
  echo "Usage patterns:"
  echo -e "  ${CYAN}nix-shell -p dafny --run \"dafny verify specs/dafny/*.dfy\"${NC}"
  echo -e "  ${CYAN}nix-shell -p tlaplus --run \"tlc specs/tla/behavior.tla -config specs/tla/behavior.cfg\"${NC}"
  echo ""
  echo "Or use the flake.nix for a persistent shell with aliases:"
  echo -e "  ${CYAN}nix develop${NC}"
  echo ""
  exit 0

else
  echo -e "  ${RED}✗${NC} nix: NOT FOUND"
  echo ""
  echo -e "${RED}Nix is required for spec-driven development.${NC}"
  echo ""
  echo "Install Nix:"
  echo "  curl -L https://nixos.org/nix/install | sh"
  echo ""
  echo "After installation, restart your shell and run this script again."
  exit 1
fi
