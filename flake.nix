{
  description = "Agda2hs";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
        packages = import ./nix/default.nix { inherit pkgs; };
        lib = import ./nix/lib.nix { inherit pkgs; };
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
