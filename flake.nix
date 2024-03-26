{
  description = "Agda2hs";

  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.mkAgdaDerivation.url = github:liesnikov/mkAgdaDerivation;

  outputs = {self, nixpkgs, flake-utils, mkAgdaDerivation}:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {inherit system;};
        haskellPackages = pkgs.haskell.packages.ghc96;
        agda2hs-hs = haskellPackages.callCabal2nixWithOptions "agda2hs" ./. "--jailbreak" {};
        agda2hs = pkgs.callPackage ./agda2hs.nix {
          inherit self;
          agda2hs = agda2hs-hs;
          inherit (haskellPackages) ghcWithPackages;
        };
        agdaDerivation = pkgs.callPackage mkAgdaDerivation.lib.mkAgdaDerivation {};
        agda2hs-lib = agdaDerivation
          { pname = "agda2hs";
            meta = {};
            version = "1.3";
            tcDir = "lib";
            src = ./.;
          };
      in {
        packages = {
          inherit agda2hs-lib;
          agda2hs = agda2hs.agda2hs;
          default = agda2hs.agda2hs;
        };
        lib = {
          withPackages = agda2hs.withPackages;
        };
        devShells.default = haskellPackages.shellFor {
          packages = p: [agda2hs-hs];
          buildInputs = with haskellPackages; [
            cabal-install
            cabal2nix
            haskell-language-server
            pkgs.agda
          ];
        };
      });
}
