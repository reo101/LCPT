{
  description = "My Lean package";

  inputs = {
    lean = {
      url = "github:leanprover/lean4";
    };
    flake-utils = {
      url = "github:numtide/flake-utils";
    };
  };

  outputs =
    { self
    , lean
    , flake-utils
    , ...
    }: flake-utils.lib.eachDefaultSystem (system:
    let
      leanPkgs = lean.packages.${system};
      pkg = leanPkgs.buildLeanPackage {
        name = "Main"; # must match the name of the top-level .lean file
        src = ./src;
      };
    in
    {
      packages = pkg // {
        inherit (leanPkgs) lean;
      };

      defaultPackage = pkg.modRoot;
    });
}
