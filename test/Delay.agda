
module Delay where

open import Haskell.Prelude
open import Haskell.Prim.Thunk
open import Haskell.Extra.Delay

open import Agda.Builtin.Size

postulate
  div : Int → Int → Int
  mod : Int → Int → Int

even : Int → Bool
even x = mod x 2 == 0

collatz : ∀ {@0 j} → Int → Delay Int j
collatz x = 
  if x == 0 then now 0
  else if even x then later (λ where .force → collatz (div x 2))
  else later λ where .force → collatz (3 * x + 1)

{-# COMPILE AGDA2HS collatz #-}
