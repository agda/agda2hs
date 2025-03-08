{-# OPTIONS --guardedness #-}

module Fail.Issue113a where

open import Haskell.Prim using (Type)

record Loop : Type where
  coinductive
  field force : Loop
open Loop public

{-# COMPILE AGDA2HS Loop unboxed #-}

loop : Loop
loop = λ where .force → loop
{-# COMPILE AGDA2HS loop #-}
