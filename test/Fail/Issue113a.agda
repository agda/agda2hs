{-# OPTIONS --guardedness #-}

module Fail.Issue113a where

record Loop : Set where
  coinductive
  field force : Loop
open Loop public

{-# COMPILE AGDA2HS Loop unboxed #-}

loop : Loop
loop = λ where .force → loop
{-# COMPILE AGDA2HS loop #-}
