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
    src = ../lib/base;
  };

  containers-lib = lib.mkDerivation {
    pname = "containers";
    meta = { };
    version = "0.8";
    buildInputs = [ base-lib ];
    everythingFile = "./agda/containers.agda";
    src = ../lib/containers;
  };
in
{
  inherit (lib) agda2hs;
  inherit base-lib containers-lib;
}
