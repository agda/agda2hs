{-# OPTIONS --polarity #-}

open import Haskell.Prelude

data Bol : Set where Tru Fls : Bol

{-# COMPILE AGDA2HS Bol gadt #-}

data Free (f : @++ Set → Set) (a : Set) : Set where
  Return : a → Free f a
  Roll : f (Free f a) → Free f a

{-# COMPILE AGDA2HS Free gadt #-}

data Na : Set where
  Ze : Na
  Su : Na → Na
{-# COMPILE AGDA2HS Na #-}

variable n : Na

data Vec (a : Set) : (n : Na) → Set where
  Nil : Vec a Ze
  Cons : (x : a) (xs : Vec a n) → Vec a (Su n)

{-# COMPILE AGDA2HS Vec gadt #-}
