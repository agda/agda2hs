module Issue93 where

open import Haskell.Prelude

fun : Bool → Bool
fun x = case x of λ where
          true  → false
          false → y
  where
    y : Bool
    y = true
{-# COMPILE AGDA2HS fun #-}

nested : Maybe Bool → Bool
nested x = case x of λ where
           (Just b) → (case y of λ where
                     true →  b
                     false → z)
           Nothing  → y
  where
    y : Bool
    y = true

    z : Bool
    z = case y of λ where
          true → y
          false → true
{-# COMPILE AGDA2HS nested #-}
