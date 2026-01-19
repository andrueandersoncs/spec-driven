#!/bin/bash
# init-specs.sh - Initialize specs/ directory structure from templates
# Usage: bash ${CLAUDE_PLUGIN_ROOT}/scripts/init-specs.sh [--force]
#
# Creates:
#   specs/
#   ├── assertions.json      # Assertion manifest
#   ├── dafny/
#   │   └── structure.dfy    # Dafny specification template
#   └── tla/
#       ├── behavior.tla     # TLA+ specification template
#       └── behavior.cfg     # TLC configuration template
#
# Options:
#   --force  : Overwrite existing files (default: skip existing)
#
# Exit codes:
#   0 - Initialization successful
#   1 - Error during initialization
#   2 - Plugin root not found

set -euo pipefail

# Determine plugin root
if [ -n "${CLAUDE_PLUGIN_ROOT:-}" ]; then
  PLUGIN_ROOT="$CLAUDE_PLUGIN_ROOT"
else
  # Try to find plugin root relative to script location
  SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  PLUGIN_ROOT="$(dirname "$SCRIPT_DIR")"
fi

TEMPLATES_DIR="$PLUGIN_ROOT/templates"
PROJECT_DIR="${CLAUDE_PROJECT_DIR:-$(pwd)}"

# Check templates exist
if [ ! -d "$TEMPLATES_DIR" ]; then
  echo "Error: Templates directory not found at $TEMPLATES_DIR" >&2
  exit 2
fi

# Parse arguments
FORCE=false
if [ "${1:-}" = "--force" ]; then
  FORCE=true
fi

# Helper function to copy template
copy_template() {
  local src="$1"
  local dest="$2"
  local desc="$3"

  if [ -f "$dest" ] && [ "$FORCE" = false ]; then
    echo "  SKIP: $desc (already exists)"
    return 0
  fi

  if [ -f "$src" ]; then
    cp "$src" "$dest"
    echo "  CREATE: $desc"
  else
    echo "  WARN: Template not found: $src" >&2
  fi
}

echo "Initializing spec-driven project structure..."
echo ""

# Create directory structure
echo "Creating directories..."
mkdir -p "$PROJECT_DIR/specs/dafny"
mkdir -p "$PROJECT_DIR/specs/tla"
echo "  CREATE: specs/"
echo "  CREATE: specs/dafny/"
echo "  CREATE: specs/tla/"
echo ""

# Copy templates
echo "Copying templates..."
copy_template "$TEMPLATES_DIR/assertions.json" "$PROJECT_DIR/specs/assertions.json" "specs/assertions.json"
copy_template "$TEMPLATES_DIR/structure.dfy" "$PROJECT_DIR/specs/dafny/structure.dfy" "specs/dafny/structure.dfy"
copy_template "$TEMPLATES_DIR/behavior.tla" "$PROJECT_DIR/specs/tla/behavior.tla" "specs/tla/behavior.tla"
copy_template "$TEMPLATES_DIR/behavior.cfg" "$PROJECT_DIR/specs/tla/behavior.cfg" "specs/tla/behavior.cfg"
echo ""

# Optionally copy flake.nix for persistent dev shell
if [ ! -f "$PROJECT_DIR/flake.nix" ]; then
  echo "Optional: Copy flake.nix for persistent Nix development shell?"
  echo "  Source: $TEMPLATES_DIR/flake.nix"
  echo "  Run: cp $TEMPLATES_DIR/flake.nix $PROJECT_DIR/"
  echo "  Then: nix develop"
  echo ""
fi

# Summary
echo "Initialization complete!"
echo ""
echo "Project structure:"
echo "  $PROJECT_DIR/"
echo "  └── specs/"
echo "      ├── assertions.json     # Define formal assertions here"
echo "      ├── dafny/"
echo "      │   └── structure.dfy   # Structural specifications"
echo "      └── tla/"
echo "          ├── behavior.tla    # Behavioral specifications"
echo "          └── behavior.cfg    # TLC configuration"
echo ""
echo "Next steps:"
echo "  1. Run /probe-domain to identify software archetype"
echo "  2. Run /interview to extract formal assertions"
echo "  3. Run /verify to check specifications"
echo "  4. Run /generate to create implementation"
