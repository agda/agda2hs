{
  pkgs ? import <nixpkgs> { },
  ...
}:
let
  hpkg = (pkgs.haskellPackages.callCabal2nix "agda2hs" ../. { }).overrideAttrs (
    finAttr: preAttr: {
      # add ./dist/build/agda2hs to $PATH
      # because cabal2nix doesn't pick up agda2hs from build-tool-depends of agda2hs-test
      # my (@liesnikov) guess is that since each cabal target is not a separate derivation
      # it's hard to form a fixpoint on a derivation level
      preCheck = ''
        export PATH=$(pwd)/dist/build/agda2hs:$PATH

        # Agda writes interface files beside its primitive library. The Nix
        # store is read-only, so give the test suite a writable data directory.
        agdaDataDir=$(agda2hs --print-agda-data-dir)
        writableAgdaDataDir="$TMPDIR/agda2hs-data"
        mkdir -p "$writableAgdaDataDir"
        cp -R "$agdaDataDir/." "$writableAgdaDataDir/"
        chmod -R u+w "$writableAgdaDataDir"
        export Agda_datadir="$writableAgdaDataDir"
      '';
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
