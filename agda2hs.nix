{stdenv, lib, self, agda2hs, runCommandNoCC, makeWrapper, writeText, mkShell, ghcWithPackages}:
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
      --add-flags "--library-file=${library-file}" \
      --add-flags "--local-interfaces"
    ''; # Local interfaces has been added for now: See https://github.com/agda/agda/issues/4526
  withPackages = arg: if builtins.isAttrs arg then withPackages' arg else withPackages' { pkgs = arg; };
in {
  inherit withPackages;
  agda2hs = withPackages [];
}
