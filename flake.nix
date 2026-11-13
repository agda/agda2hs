{
  description = "Agda2hs";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.agda = {
    url = "github:agda/agda/v2.9.0";
    flake = false;
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      agda,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
        packages = import ./nix/default.nix {
          inherit pkgs;
          agdaSrc = agda;
        };
        lib = import ./nix/lib.nix {
          inherit pkgs;
          agdaSrc = agda;
        };
      in
      {
        packages = packages // {
          default = packages.agda2hs;
        };
        inherit lib;
        devShells.default = import ./nix/shell.nix {
          inherit pkgs;
          inherit (lib) agda2hs-hs;
        };
      }
    );
}
