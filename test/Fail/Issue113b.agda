{-# OPTIONS --guardedness #-}

module Fail.Issue113b where

open import Haskell.Prim using (Type)

postulate A : Type

record Loop : Type where
  coinductive
  field force : Loop
open Loop public

{-# COMPILE AGDA2HS Loop unboxed #-}

loop : {@0 x : A} → Loop
loop {x} = λ where .force → loop {x}
{-# COMPILE AGDA2HS loop #-}
