module Haskell.Data.Ord where

open import Haskell.Prelude

comparing : ⦃ Ord a ⦄ → (b → a) → b → b → Ordering
comparing p x y = compare (p x) (p y)

clamp : ⦃ Ord a ⦄ → (a × a) → a → a
clamp (low , high) a = min high (max a low)
