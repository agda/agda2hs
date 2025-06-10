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
        # Override haskellPackages.Agda with a candidate from Hackage.
        pkgver = "Agda-2.7.20250601";
        sha256 = "sha256-ng/ijIIdiJqGrlqTt36rpO38XHFRuvhDUr0Z58P7eaw=";
        overlayHaskellPackages = self: super: {
          haskellPackages = super.haskellPackages.override {
            overrides = new: old:
              let
                Agda_plain = old.callCabal2nix "Agda" (super.fetchzip {
                  url = "mirror://hackage/${pkgver}/candidate/${pkgver}.tar.gz";
                  inherit sha256;
                }) {};
              in {
                # Mirror the flag overrides done by nixpkgs
                # in order to make  pkgs.agdaPackages.mkDerivation  work.
                Agda = super.lib.pipe Agda_plain [
                  (super.haskell.lib.compose.enableCabalFlag "optimise-heavily")
                  (super.haskell.lib.compose.enableCabalFlag "debug")
                  super.haskell.lib.compose.enableSeparateBinOutput
                ];
              };
          };
        };

        pkgs = import nixpkgs {
          inherit system;
          overlays = [ overlayHaskellPackages ];
        };
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
