module Fail.Issue71 where

open import Haskell.Prelude

scanrList : (a → b → b) → b → List a → List b
scanrList f z [] = z ∷ []
scanrList f z (x ∷ xs) =
  case scanrList f z xs of λ {
    [] -> []
  ; qs@(q ∷ _) -> f x q ∷ qs
  }
{-# COMPILE AGDA2HS scanrList #-}
