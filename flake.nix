{
  description = "Specification for haskell modules";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
    let 
      pkgs = import nixpkgs {
        inherit system;
        overlays = [ (lean4-nix.readToolchainFile ./lean/lean-toolchain) ];
      };
    in {
      formatter = pkgs.nixpkgs-fmt;

      devShell = pkgs.mkShell {
        buildInputs = with pkgs; [
          lean
          # Haskell
          cabal-install
          haskell-language-server
          ghc
        ];
      };
    });
}

