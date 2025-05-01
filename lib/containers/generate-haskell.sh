#!/bin/sh
ROOT=containers.agda
AGDA2HS="cabal run agda2hs --"
${AGDA2HS} \
    --local-interfaces \
    --no-default-libraries \
    --library-file ./agda2hs-libraries \
    -o ./haskell/ \
    ./agda/${ROOT}
