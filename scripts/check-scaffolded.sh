#!/bin/bash
# check-scaffolded.sh - Check if project is properly scaffolded for execution
# Usage: bash ${CLAUDE_PLUGIN_ROOT}/scripts/check-scaffolded.sh [--json|--quiet]
#
# Checks for:
#   - package.json exists
#   - node_modules/ or bun.lockb exists (dependencies installed)
#   - src/ directory exists
#   - tests/ directory exists (optional but recommended)
#
# Output modes:
#   (default)  : Human-readable status with recommendations
#   --json     : JSON object with detailed status
#   --quiet    : No output, only exit code
#
# Exit codes:
#   0 - Project is scaffolded and ready
#   1 - Project is not scaffolded (needs /scaffold)
#   2 - Partially scaffolded (missing dependencies)

set -euo pipefail

PROJECT_DIR="${CLAUDE_PROJECT_DIR:-$(pwd)}"
OUTPUT_MODE="${1:-default}"

# Check components
has_package_json=false
has_dependencies=false
has_src=false
has_tests=false
has_tsconfig=false

[ -f "$PROJECT_DIR/package.json" ] && has_package_json=true
[ -d "$PROJECT_DIR/node_modules" ] || [ -f "$PROJECT_DIR/bun.lockb" ] && has_dependencies=true
[ -d "$PROJECT_DIR/src" ] && has_src=true
[ -d "$PROJECT_DIR/tests" ] && has_tests=true
[ -f "$PROJECT_DIR/tsconfig.json" ] && has_tsconfig=true

# Determine overall status
if [ "$has_package_json" = true ] && [ "$has_dependencies" = true ] && [ "$has_src" = true ]; then
  status="ready"
  exit_code=0
elif [ "$has_package_json" = true ] && [ "$has_src" = true ]; then
  status="needs_install"
  exit_code=2
elif [ "$has_package_json" = true ]; then
  status="partial"
  exit_code=2
else
  status="not_scaffolded"
  exit_code=1
fi

case "$OUTPUT_MODE" in
  --json)
    cat <<EOF
{
  "status": "$status",
  "checks": {
    "package_json": $has_package_json,
    "dependencies": $has_dependencies,
    "src_directory": $has_src,
    "tests_directory": $has_tests,
    "tsconfig": $has_tsconfig
  },
  "ready": $([ "$status" = "ready" ] && echo "true" || echo "false")
}
EOF
    ;;

  --quiet)
    # No output
    ;;

  *)
    echo "Project Scaffold Status"
    echo "======================="
    echo ""

    # Package.json
    if [ "$has_package_json" = true ]; then
      echo "  [x] package.json"
    else
      echo "  [ ] package.json - MISSING"
    fi

    # Dependencies
    if [ "$has_dependencies" = true ]; then
      echo "  [x] dependencies installed"
    else
      echo "  [ ] dependencies - NOT INSTALLED"
    fi

    # Source directory
    if [ "$has_src" = true ]; then
      echo "  [x] src/ directory"
    else
      echo "  [ ] src/ directory - MISSING"
    fi

    # Tests (optional)
    if [ "$has_tests" = true ]; then
      echo "  [x] tests/ directory"
    else
      echo "  [ ] tests/ directory - MISSING (optional)"
    fi

    # TypeScript config
    if [ "$has_tsconfig" = true ]; then
      echo "  [x] tsconfig.json"
    else
      echo "  [ ] tsconfig.json - MISSING"
    fi

    echo ""

    case "$status" in
      ready)
        echo "Status: READY"
        echo "Project is fully scaffolded and ready for development."
        ;;
      needs_install)
        echo "Status: NEEDS INSTALL"
        echo "Run: bun install"
        ;;
      partial)
        echo "Status: PARTIAL"
        echo "Some components missing. Run /scaffold to complete setup."
        ;;
      not_scaffolded)
        echo "Status: NOT SCAFFOLDED"
        echo "Run /scaffold to create project infrastructure."
        ;;
    esac
    ;;
esac

exit $exit_code
