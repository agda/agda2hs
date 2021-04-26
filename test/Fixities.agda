
module Fixities where

open import Haskell.Prelude

leftAssoc : Int → List Int
leftAssoc n = 2 * n + 1
            ∷ 2 * (n + 1)
            ∷ 1 + n * 2
            ∷ (1 + n) * 2
            ∷ (n + n) + n
            ∷ n + (n + n)
            ∷ []

rightAssoc : List Int → List Int
rightAssoc xs = xs ++ xs ++ ((xs ++ xs) ++ xs) ++ xs

nonAssoc : Bool → Bool
nonAssoc b = (b == b) == (b == b)

mixedAssoc : Maybe Int → (Int → Maybe Int) → Maybe Int
mixedAssoc m f = f =<< (((f =<< m) >>= f) >>= f)

{-# COMPILE AGDA2HS leftAssoc  #-}
{-# COMPILE AGDA2HS rightAssoc #-}
{-# COMPILE AGDA2HS nonAssoc   #-}
{-# COMPILE AGDA2HS mixedAssoc #-}
