module CompileToAlphaDataTarget where

open import Haskell.Prelude

data Target (a : Set) : Set₁ where
  MkTarget : (∀ {x : Set} → x → x) → a → Target a

{-# COMPILE AGDA2HS Target #-}
