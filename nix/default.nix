{
  pkgs ? import <nixpkgs> { },
  ...
}:
let
  lib = import ./lib.nix { inherit pkgs; };
  version = "1.3";

  base-lib = lib.mkDerivation {
    pname = "base";
    meta = { };
    version = "4.18";
    preBuild = ''
      echo "{-# OPTIONS --sized-types #-}" > Everything.agda
      echo "module Everything where" >> Everything.agda
      find . -name '*.agda' ! -name 'Everything.agda' | sed -e 's/.\///;s/\//./g;s/\.agda$//;s/^/import /' >> Everything.agda
    '';
    src = ../lib/base;
  };
in
{
  inherit (lib) agda2hs;
  inherit base-lib;
}
