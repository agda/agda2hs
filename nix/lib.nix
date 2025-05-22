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
  hpkg = pkgs.haskellPackages.callPackage (hsrc "") { };
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
