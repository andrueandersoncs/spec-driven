{
  description = "Spec-driven development environment with Dafny, TLA+, and Bun";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # TLA+ tools JAR path
        tla2toolsJar = "${pkgs.tlaplus}/share/java/tla2tools.jar";
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            # ==========================================
            # Formal Verification Tools
            # ==========================================

            # Dafny - Verification-aware programming language
            # Used for structural specifications (data constraints, contracts)
            # Docs: https://dafny.org/latest/DafnyRef/DafnyRef
            pkgs.dafny

            # TLA+ Toolbox - Formal specification language tools
            # Used for behavioral specifications (state machines, temporal properties)
            # Includes: TLC model checker, SANY parser, PlusCal translator
            # Docs: https://github.com/tlaplus/tlaplus
            pkgs.tlaplus

            # Java runtime required for TLA+ tools
            pkgs.openjdk17

            # ==========================================
            # Runtime & Development
            # ==========================================

            # Bun - Fast JavaScript/TypeScript runtime and package manager
            # Used for running generated TypeScript code
            # Docs: https://bun.sh/docs
            pkgs.bun

            # TypeScript - for type checking (tsc --noEmit)
            pkgs.typescript

            # ==========================================
            # Deployment (optional)
            # ==========================================

            # Docker CLI for containerization
            # Used by /deploy command
            pkgs.docker-client

            # ==========================================
            # Utilities
            # ==========================================

            # JSON processing - used by hooks and assertions.json manipulation
            pkgs.jq

            # GraphViz - for TLA+ state graph visualization
            # tlc -dump dot states.dot creates DOT files
            pkgs.graphviz

            # Shell script linting (for validating hook scripts)
            pkgs.shellcheck

            # Watch files and run commands (for development)
            pkgs.watchexec
          ];

          shellHook = ''
            echo ""
            echo "╔══════════════════════════════════════════════════════════════╗"
            echo "║  🔬 Spec-Driven Development Environment                      ║"
            echo "╚══════════════════════════════════════════════════════════════╝"
            echo ""

            # Set up TLA+ tools path
            export TLA2TOOLS_JAR="${tla2toolsJar}"

            # ==========================================
            # Tool Version Check
            # ==========================================
            echo "Tool versions:"
            echo "  Dafny:      $(dafny --version 2>/dev/null | head -1 || echo 'not found')"
            echo "  TLC:        $(java -jar $TLA2TOOLS_JAR -h 2>&1 | grep -m1 Version || echo 'available')"
            echo "  Bun:        $(bun --version 2>/dev/null || echo 'not found')"
            echo "  TypeScript: $(tsc --version 2>/dev/null || echo 'not found')"
            echo ""

            # ==========================================
            # Aliases for Common Operations
            # ==========================================

            # TLC with performance optimizations (parallel GC, auto workers)
            # See: https://docs.tlapl.us/using:tlc:start
            alias tlc="java -XX:+UseParallelGC -jar $TLA2TOOLS_JAR"

            # TLC with 4 workers (adjust based on your CPU)
            alias tlc4="java -XX:+UseParallelGC -jar $TLA2TOOLS_JAR -workers 4"

            # TLC in simulation mode (for large state spaces)
            alias tlc-sim="java -XX:+UseParallelGC -jar $TLA2TOOLS_JAR -simulate"

            # SANY - TLA+ syntax checker/parser
            alias sany="java -cp $TLA2TOOLS_JAR tla2sany.SANY"

            # PlusCal translator
            alias pcal="java -cp $TLA2TOOLS_JAR pcal.trans"

            # Quick verification commands
            alias verify-dafny="dafny verify specs/dafny/*.dfy"
            alias verify-tla="tlc specs/tla/behavior.tla -config specs/tla/behavior.cfg"
            alias verify-all="verify-dafny && verify-tla"

            echo "Quick commands:"
            echo "  verify-dafny   - Verify all Dafny specs"
            echo "  verify-tla     - Model check TLA+ specs"
            echo "  verify-all     - Run all verifications"
            echo "  tlc            - TLC with performance options"
            echo "  tlc4           - TLC with 4 workers"
            echo "  tlc-sim        - TLC simulation mode"
            echo "  sany           - TLA+ syntax checker"
            echo ""

            # ==========================================
            # Project Detection
            # ==========================================
            if [ -d "specs" ]; then
              echo "📁 Spec-driven project detected"
              if [ -f "specs/assertions.json" ]; then
                total=$(jq '.assertions | length' specs/assertions.json 2>/dev/null || echo "0")
                confirmed=$(jq '[.assertions[] | select(.status == "confirmed")] | length' specs/assertions.json 2>/dev/null || echo "0")
                echo "   Assertions: $total total ($confirmed confirmed)"
              fi
              dafny_count=$(find specs/dafny -name "*.dfy" 2>/dev/null | wc -l | tr -d ' ')
              tla_count=$(find specs/tla -name "*.tla" 2>/dev/null | wc -l | tr -d ' ')
              [ "$dafny_count" -gt 0 ] && echo "   Dafny specs: $dafny_count files"
              [ "$tla_count" -gt 0 ] && echo "   TLA+ specs: $tla_count files"
              echo ""
            fi

            echo "Run 'exit' to leave the development shell"
            echo ""
          '';
        };

        # Optional: Add a check for tool availability
        checks.default = pkgs.runCommand "check-tools" {} ''
          ${pkgs.dafny}/bin/dafny --version
          java -jar ${tla2toolsJar} -h 2>&1 | head -1
          ${pkgs.bun}/bin/bun --version
          touch $out
        '';
      });
}
