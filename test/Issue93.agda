module Issue93 where

open import Haskell.Prelude

fun : Bool → Bool
fun x = case x of λ where
          True  → False
          False → y
  where
    y : Bool
    y = True
{-# COMPILE AGDA2HS fun #-}

nested : Maybe Bool → Bool
nested x = case x of λ where
           (Just b) → (case y of λ where
                     True →  b
                     False → z)
           Nothing  → y
  where
    y : Bool
    y = True

    z : Bool
    z = case y of λ where
          True → y
          False → True
{-# COMPILE AGDA2HS nested #-}
