open import Haskell.Prelude

mapMaybeB : (a → b) → Maybe a → Maybe b
mapMaybeB = λ where
  f Nothing  → Nothing
  f (Just x) → Just (f x)

{-# COMPILE AGDA2HS mapMaybeB #-}
