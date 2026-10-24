{
  pkgs ? import <nixpkgs> { },
  agdaSrc ? null,
  ...
}:
let
  # cabal2nix ignores source-repository-package entries in cabal.project, so
  # use the same pinned Agda source explicitly for the Nix build.
  agdaPackage =
    if agdaSrc == null then
      pkgs.haskellPackages.Agda
    else
      pkgs.haskellPackages.callCabal2nix "Agda" agdaSrc { };
  hpkg = (pkgs.haskellPackages.callCabal2nix "agda2hs" ../. {
    Agda = agdaPackage;
  }).overrideAttrs (
    finAttr: preAttr: {
      # add ./dist/build/agda2hs to $PATH
      # because cabal2nix doesn't pick up agda2hs from build-tool-depends of agda2hs-test
      # my (@liesnikov) guess is that since each cabal target is not a separate derivation
      # it's hard to form a fixpoint on a derivation level
      preCheck = "export PATH=$(pwd)/dist/build/agda2hs:$PATH";
    });
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
  agda2hs-hs = hpkg;
  agda2hs-expr = expr;
  inherit (agda2hs) agda2hs withPackages mkDerivation;
}
