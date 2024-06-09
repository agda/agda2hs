module Fail.Issue119 where

open import Haskell.Prelude

aaa : Int
aaa = 21

-- Oops, forgot compile pragma for aaa

bbb : Int
bbb = aaa + aaa

{-# COMPILE AGDA2HS bbb #-}
