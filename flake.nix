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

        withCompiler = compiler:
          let haskellPackages =
                if compiler == "default"
                then pkgs.haskellPackages
                else pkgs.haskell.packages.${compiler};
              agda2hs-hs =
                haskellPackages.callCabal2nixWithOptions "agda2hs" ./. "--jailbreak" {};
          in pkgs.callPackage ./agda2hs.nix {
            inherit self;
            agda2hs = agda2hs-hs;
            inherit (haskellPackages) ghcWithPackages;
          };
        agda2hs = withCompiler "default";

        agda2hs-hs =
          pkgs.haskellPackages.callCabal2nixWithOptions "agda2hs" ./. "--jailbreak" {};
      in {
        packages = {
          inherit agda2hs-lib;
          agda2hs = agda2hs.agda2hs;
          default = agda2hs.agda2hs;
        };
        lib = {
          withPackages = agda2hs.withPackages;
          inherit withCompiler;
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
