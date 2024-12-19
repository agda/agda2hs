{
  pkgs ? import <nixpkgs> { },
  ...
}:
let
  lib = import ./lib.nix { inherit pkgs; };
  version = "1.3";
  agdalib = pkgs.agdaPackages.mkDerivation {
    pname = "agda2hs";
    meta = { };
    version = version;
    preBuild = ''
      echo "{-# OPTIONS --sized-types #-}" > Everything.agda
      echo "module Everything where" >> Everything.agda
      find lib -name '*.agda' | sed -e 's/lib\///;s/\//./g;s/\.agda$//;s/^/import /' >> Everything.agda
    '';
    src = ../.;
  };
in
{
  inherit (lib) agda2hs;
  agda2hs-lib = agdalib;
}
