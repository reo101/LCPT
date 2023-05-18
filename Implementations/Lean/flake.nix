{
  description = "My Lean package";

  inputs = {
    nixpkgs = {
      url = "github:NixOS/nixpkgs/nixos-unstable";
    };
    lean = {
      url = "github:leanprover/lean4";
    };
    flake-utils = {
      url = "github:numtide/flake-utils";
    };
  };

  outputs =
    { self
    , nixpkgs
    , lean
    , flake-utils
    , ...
    }: flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = nixpkgs.legacyPackages.${system};
      leanPkgs = lean.packages.${system};
      pkg = leanPkgs.buildLeanPackage {
        name = "Main";
        src = ./src;
        fullSrc = ./.;
      };
    in
    {
      packages = pkg // {
        inherit (leanPkgs) lean;
        default = pkg.modRoot;
      };

      devShells = rec {
        lean-dev = pkgs.mkShell {
          buildInputs = [
            pkg.lean-dev
          ];
        };

        default = lean-dev;
      };
    });
}
