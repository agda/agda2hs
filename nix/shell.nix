{
  pkgs ? import <nixpkgs> { },
  agda2hs-hs ? (import ./lib.nix { inherit pkgs; }).agda2hs-hs,
}:
pkgs.haskellPackages.shellFor {
  # This doesn't result in a shell where you can use cabal (v2-)build,
  # due to build-tool-depends in Agda's .cabal file, so for now only v1-build works
  # Making cabal re-install alex and happy from Hackage can work,
  # which will be done if the user runs `cabal update` and `cabal build`.
  # relevant issues listed in:
  # https://gist.github.com/ScottFreeCode/ef9f254e2dd91544bba4a068852fc81f
  # main ones are:
  # https://github.com/haskell/cabal/issues/8434
  # https://github.com/NixOS/nixpkgs/issues/130556
  # https://github.com/NixOS/nixpkgs/issues/176887
  packages = p: [ agda2hs-hs ];
  nativeBuildInputs = with pkgs.haskellPackages; [
    # related to haskell
    cabal-install
    # FIXME: broken in haskell-updates, uncomment when upstream fixes it
    haskell-language-server
    # general goodies
    pkgs.agda
    pkgs.nixfmt-rfc-style
    cabal2nix
  ];
}
