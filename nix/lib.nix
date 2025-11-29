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
  # Disable tests in nix build - the testsuite requires the agda2hs binary
  # to be in PATH, which is a circular dependency. Tests should be run
  # via `cabal test` in a development environment instead.
  hpkg = pkgs.haskell.lib.dontCheck (pkgs.haskellPackages.callPackage (hsrc "") { });
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
