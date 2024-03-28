{
  description = "Agda2hs";

  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.mkAgdaDerivation.url = github:liesnikov/mkAgdaDerivation;

  outputs = {self, nixpkgs, flake-utils, mkAgdaDerivation}:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {inherit system;};

        agdaDerivation =
          pkgs.callPackage mkAgdaDerivation.lib.mkAgdaDerivation {};
        agda2hs-lib = agdaDerivation
          { pname = "agda2hs";
            meta = {};
            version = "1.3";
            tcDir = "lib";
            src = ./.;
          };
        agda2hs-pkg = options:
          pkgs.haskellPackages.haskellSrc2nix {
            name = "agda2hs";
            src = ./.;
            extraCabal2nixOptions = options;
        };
        agda2hs-hs = pkgs.haskellPackages.callPackage (agda2hs-pkg "--jailbreak") {};
        agda2hs-expr = import ./agda2hs.nix;
        agda2hs = pkgs.callPackage agda2hs-expr {
            inherit self;
            agda2hs = agda2hs-hs;
            inherit (pkgs.haskellPackages) ghcWithPackages;
          };
      in {
        packages = {
          inherit agda2hs-lib;
          inherit (agda2hs) agda2hs;
          default = agda2hs.agda2hs;
        };
        lib = {
          inherit (agda2hs) withPackages;
          inherit agda2hs-pkg agda2hs-hs agda2hs-expr;
        };
        devShells.default = pkgs.haskellPackages.shellFor {
          packages = p: [agda2hs-pkg];
          buildInputs = with pkgs.haskellPackages; [
            cabal-install
            cabal2nix
            haskell-language-server
            pkgs.agda
          ];
        };
      });
}
