{
  description = "Agda2hs";

  inputs.nixpkgs.url = github:NixOS/nixpkgs;
  inputs.flake-utils.url = github:numtide/flake-utils;

  outputs = {self, nixpkgs, flake-utils}:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {inherit system;};

        agda2hs-lib = pkgs.agdaPackages.mkDerivation
          { pname = "agda2hs";
            meta = {};
            version = "1.3";
            preBuild = ''
              echo "{-# OPTIONS --sized-types #-}" > Everything.agda
              echo "module Everything where" >> Everything.agda
              find lib -name '*.agda' | sed -e 's/lib\///;s/\//./g;s/\.agda$//;s/^/import /' >> Everything.agda
            '';
            src = ./.;
          };
        # options provides a way to jailbreak for packages that use agda2hs
        agda2hs-pkg = options:
          pkgs.haskellPackages.haskellSrc2nix {
            name = "agda2hs";
            src = ./.;
            extraCabal2nixOptions = options; #"--jailbreak"
        };
        agda2hs-hs = pkgs.haskellPackages.callPackage (agda2hs-pkg "") {};
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
          packages = p: [agda2hs-hs];
          buildInputs = with pkgs.haskellPackages; [
            cabal-install
            cabal2nix
            haskell-language-server
            pkgs.agda
          ];
        };
      });
}
