{ nixpkgs ? import <nixpkgs> { }, compiler ? "default", doBenchmark ? false }:

let

  inherit (nixpkgs) pkgs;

  f =
    { mkDerivation
    , Agda
    , base
    , containers
    , haskell-src-exts
    , stdenv
    }:
    mkDerivation {
      pname = "agda2hs";
      version = "1.0";
      src = ./.;
      isLibrary = false;
      isExecutable = true;
      executableHaskellDepends = [
        Agda
        base
        containers
        haskell-src-exts
      ];
      description = "Compiling Agda code to readable Haskell";
      license = stdenv.lib.licenses.bsd3;
    };

  haskellPackages =
    if compiler == "default"
    then pkgs.haskellPackages
    else pkgs.haskell.packages.${compiler};

  variant = if doBenchmark then pkgs.haskell.lib.doBenchmark else pkgs.lib.id;

  drv = variant (haskellPackages.callPackage f { });

in

if pkgs.lib.inNixShell then drv.env else drv
