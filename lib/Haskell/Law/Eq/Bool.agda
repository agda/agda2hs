module Haskell.Law.Eq.Bool where

open import Haskell.Prim
open import Haskell.Prim.Eq

open import Haskell.Law.Eq.Def

instance
  iLawfulEqBool : IsLawfulEq Bool
  iLawfulEqBool .equality False False _ = refl
  iLawfulEqBool .equality True True _ = refl

  iLawfulEqBool .nequality False True _ = λ()
  iLawfulEqBool .nequality True False _ = λ()
 