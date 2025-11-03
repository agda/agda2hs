open import Haskell.Prelude

module Fail.Issue306a where

cast : {a b : Set} → @0 a ≡ b → a → b
cast {a} {b} = cast'
  where
  cast' : @0 a ≡ b → a → b
  cast' refl x = x

{-# COMPILE AGDA2HS cast #-}
