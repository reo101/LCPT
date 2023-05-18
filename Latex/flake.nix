{
  inputs = {
    nixpkgs = {
      url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    };
    flake-utils = {
      url = "github:numtide/flake-utils";
    };
    # zig-overlay = {
    #   url = "github:mitchellh/zig-overlay";
    #   inputs.nixpkgs.follows = "nixpkgs";
    # };
  };

  outputs =
    { self
    , nixpkgs
    , flake-utils
    # , zig-overlay
    , ...
    } @ inputs : flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            # zig-overlay.overlays.default
          ];
        };
      in
      with pkgs; {
        devShell = mkShell {
          buildInputs = [
            ### Main

            texlab
            texlive.combined.scheme-full
          ];
        };
    });
}
