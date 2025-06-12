#!/bin/sh
ROOT=Containers.agda
AGDA2HS="cabal run agda2hs --"
${AGDA2HS} \
    --no-default-libraries \
    --library-file ./agda2hs-libraries \
    -o ./haskell/ \
    ./agda/${ROOT}
