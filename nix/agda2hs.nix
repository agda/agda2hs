# This file should be very close to a copy of nixpkgs/pkgs/build-support/agda/default.nix
# The present file is based on https://github.com/NixOS/nixpkgs/blob/1d2cfef5e965ca6933a8aa696eadfa556d90fab3/pkgs/build-support/agda/default.nix
# FIXME: this file is haskell-updates, double-check that nothing changes once it gets merged in unstable
# but it would be nice to expose this in upstream so that we don't have to duplicate the file

{
  stdenv,
  lib,
  self,
  agda2hs,
  runCommand,
  makeWrapper,
  writeText,
  ghcWithPackages,
}:

let
  inherit (lib)
    elem
    filter
    filterAttrs
    isAttrs
    isList
    platforms
    ;

  inherit (lib.strings)
    concatMapStringsSep
    optionalString
    ;

  mkLibraryFile =
    pkgs:
    let
      pkgs' = if isList pkgs then pkgs else pkgs self;
    in
    writeText "libraries" ''
      ${(concatMapStringsSep "\n" (p: "${p}/${p.libraryFile}") pkgs')}
    '';

  withPackages' =
    {
      pkgs,
      ghc ? ghcWithPackages (p: with p; [ ieee754 ]),
    }:
    let
      library-file = mkLibraryFile pkgs;
      pname = "agda2hsWithPackages";
      version = agda2hs.version;
    in
    runCommand "${pname}-${version}"
      {
        inherit pname version;
        nativeBuildInputs = [ makeWrapper ];
        passthru = {
          unwrapped = agda2hs;
          inherit withPackages;
        };
        meta = agda2hs.meta;
      }
      ''
        mkdir -p $out/bin
        makeWrapper ${agda2hs}/bin/agda2hs $out/bin/agda2hs \
          ${lib.optionalString (ghc != null) ''--add-flags "--with-compiler=${ghc}/bin/ghc"''} \
          --add-flags "--library-file=${library-file}"
      '';

  withPackages = arg: if isAttrs arg then withPackages' arg else withPackages' { pkgs = arg; };

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
      libraryName ? pname,
      libraryFile ? "${libraryName}.agda-lib",
      buildPhase ? null,
      installPhase ? null,
      extraExtensions ? [ ],
      ...
    }:
    let
      agdaWithPkgs = withPackages (filter (p: p ? isAgdaDerivation) buildInputs);
    in
    {
      inherit libraryName libraryFile;

      isAgdaDerivation = true;

      buildInputs = buildInputs ++ [ agdaWithPkgs ];

      buildPhase =
        if buildPhase != null then
          buildPhase
        else
          ''
            runHook preBuild
            agda2hs --build-library
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

      meta = if meta.broken or false then meta // { hydraPlatforms = platforms.none; } else meta;
    };
in
{
  mkDerivation = args: stdenv.mkDerivation (args // defaults args);

  inherit mkLibraryFile withPackages withPackages';
  agda2hs = withPackages [];
}
