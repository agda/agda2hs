{
  pkgs ? import <nixpkgs> { },
  ...
}:
let
  hsrc =
    options:
    pkgs.haskellPackages.haskellSrc2nix {
      name = "agda2hs";
      src = ../.;
      extraCabal2nixOptions = options; # "--jailbreak"
    };
  hpkg = (pkgs.haskellPackages.callPackage (hsrc "") {}).overrideAttrs (
    finAttr: preAttr: {
      # make executables executable and add ./dist/build to PATH
      # cabal2nix doesn't pick up agda2hs from build-tool-depends of the test suite
      # my (@liesnikov) guess is that since the intermediate binary
      # is not a separate derivation it's hard to form a fixpoint on a derivation level
      preCheck = ''
        find dist/build -exec chmod u+X {} +
        export PATH=$(pwd)/dist/build/:$PATH
      '';
    }
  );
  expr = import ./agda2hs.nix;
  agda2hs = pkgs.lib.makeScope pkgs.newScope (
    self:
    pkgs.callPackage expr {
      agda2hs = hpkg;
      inherit self;
      inherit (pkgs.haskellPackages) ghcWithPackages;
    }
  );
in
{
  agda2hs-pkg = hsrc;
  agda2hs-hs = hpkg;
  agda2hs-expr = expr;
  inherit (agda2hs) agda2hs withPackages mkDerivation;
}
