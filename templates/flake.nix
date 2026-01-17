{
  description = "Spec-driven development environment with Dafny and TLA+";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            # Dafny - Formal verification language
            dafny

            # Java runtime for TLC model checker
            openjdk17

            # TLA+ tools (TLC model checker, TLAPS proof system)
            tlaplus
            tlaplus18  # Alternative if tlaplus has issues

            # Node.js for TypeScript development
            nodejs_20
            nodePackages.typescript
            nodePackages.typescript-language-server

            # Useful utilities
            jq          # JSON processing
            yq          # YAML processing
            graphviz    # For TLA+ state graph visualization
          ];

          shellHook = ''
            echo "🔬 Spec-driven development environment ready"
            echo ""
            echo "Available tools:"
            echo "  dafny     - Formal verification (structure specs)"
            echo "  tlc       - TLA+ model checker (behavior specs)"
            echo "  node/npm  - TypeScript development"
            echo ""
            echo "Quick commands:"
            echo "  dafny verify specs/dafny/*.dfy     - Verify Dafny specs"
            echo "  tlc specs/tla/behavior.tla        - Model check TLA+ specs"
            echo "  dafny build --target:js ...       - Extract to JavaScript"
            echo ""

            # Set up TLA+ tools path
            export TLA2TOOLS_JAR="${pkgs.tlaplus}/share/java/tla2tools.jar"

            # Alias for TLC with common options
            alias tlc="java -cp $TLA2TOOLS_JAR tlc2.TLC"

            # Alias for SANY (TLA+ parser)
            alias sany="java -cp $TLA2TOOLS_JAR tla2sany.SANY"
          '';
        };
      });
}
