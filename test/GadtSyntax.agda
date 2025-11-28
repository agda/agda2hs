{-# OPTIONS --polarity #-}

open import Haskell.Prelude

data Bol : Set where Tru Fls : Bol

{-# COMPILE AGDA2HS Bol gadt #-}

data Free (f : @++ Set → Set) (a : Set) : Set where
  Return : a → Free f a
  Roll : f (Free f a) → Free f a

{-# COMPILE AGDA2HS Free gadt #-}
