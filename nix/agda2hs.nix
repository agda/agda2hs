# This file should be very close to a copy of nixpkgs/pkgs/build-support/agda/default.nix
# The present file appears to be an amalgaman of
#   https://github.com/NixOS/nixpkgs/blob/bbe6402ecacfc3a0e2c65e3527c2cbe148b98ff8/pkgs/build-support/agda/default.nix
#   https://github.com/NixOS/nixpkgs/blob/583eef75e722741878b186f5bdf5a826d638f868/pkgs/build-support/agda/default.nix
# but it would be nice to expose this in upstream so that we don't have to duplicate the file
{
  stdenv,
  lib,
  self,
  agda2hs,
  runCommandNoCC,
  makeWrapper,
  writeText,
  ghcWithPackages,
}:

with lib.strings;
let
  withPackages' = {
      pkgs,
      ghc ? ghcWithPackages (p: with p; [ ieee754 ])
  }: let
    pkgs' = if builtins.isList pkgs then pkgs else pkgs self;
    library-file = writeText "libraries" ''
      ${(concatMapStringsSep "\n" (p: "${p}/${p.libraryFile}") pkgs')}
    '';
    pname = "agda2hsWithPackages";
    version = agda2hs.version;
  in runCommandNoCC "${pname}-${version}" {
    inherit pname version;
    nativeBuildInputs = [ makeWrapper ];
    passthru.unwrapped = agda2hs;
  } ''
    mkdir -p $out/bin
    makeWrapper ${agda2hs}/bin/agda2hs $out/bin/agda2hs \
      --add-flags "--with-compiler=${ghc}/bin/ghc" \
      --add-flags "--library-file=${library-file}"
    '';
  withPackages = arg: if builtins.isAttrs arg then withPackages' arg else withPackages' { pkgs = arg; };

  extensions = [
    "agda"
    "agda-lib"
    "agdai"
    "lagda"
    "lagda.md"
    "lagda.org"
    "lagda.rst"
    "lagda.tex"
    "lagda.typ"
  ];

  defaults =
    {
      pname,
      meta,
      buildInputs ? [ ],
      everythingFile ? "./Everything.agda",
      includePaths ? [ ],
      libraryName ? pname,
      libraryFile ? "${libraryName}.agda-lib",
      buildPhase ? null,
      installPhase ? null,
      extraExtensions ? [ ],
      ...
    }:
    let
      agdaWithArgs = withPackages (filter (p: p ? isAgdaDerivation) buildInputs);
      includePathArgs = concatMapStrings (path: "-i" + path + " ") (
        includePaths ++ [ (dirOf everythingFile) ]
      );
    in
    {
      inherit libraryName libraryFile;

      isAgdaDerivation = true;

      buildInputs = buildInputs ++ [ agdaWithArgs ];

      buildPhase =
        if buildPhase != null then
          buildPhase
        else
          ''
            runHook preBuild
            agda2hs ${includePathArgs} ${everythingFile}
            rm ${everythingFile} ${everythingFile}i
            runHook postBuild
          '';

      installPhase =
        if installPhase != null then
          installPhase
        else
          ''
            runHook preInstall
            mkdir -p $out
            find \( ${
              concatMapStringsSep " -or " (p: "-name '*.${p}'") (extensions ++ extraExtensions)
            } \) -exec cp -p --parents -t "$out" {} +
            runHook postInstall
          '';

      # As documented at https://github.com/NixOS/nixpkgs/issues/172752,
      # we need to set LC_ALL to an UTF-8-supporting locale. However, on
      # darwin, it seems that there is no standard such locale; luckily,
      # the referenced issue doesn't seem to surface on darwin. Hence let's
      # set this only on non-darwin.
      LC_ALL = optionalString (!stdenv.hostPlatform.isDarwin) "C.UTF-8";
    };

in {
  mkDerivation = args: stdenv.mkDerivation (args // defaults args);

  inherit withPackages;
  agda2hs = withPackages [];
}
