{
  description = "Agda2hs";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.agda = {
    url = "github:agda/agda/f26c433f6eaf0bb2345e87358a5dbaca347bc828";
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
