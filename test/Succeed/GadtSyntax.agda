{-# OPTIONS --polarity #-}

open import Haskell.Prelude

{-# FOREIGN AGDA2HS
{-# LANGUAGE DataKinds #-}
#-}

data Bol : Type where Tru Fls : Bol

{-# COMPILE AGDA2HS Bol gadt #-}

data Free (f : @++ Type → Type) (a : Type) : Type where
  Return : a → Free f a
  Roll : f (Free f a) → Free f a

{-# COMPILE AGDA2HS Free gadt #-}

data Color : Type where
  Red Green : Color

{-# COMPILE AGDA2HS Color gadt deriving ( Show ) #-}

data Na : Type where
  Ze : Na
  Su : Na → Na
{-# COMPILE AGDA2HS Na #-}

variable n : Na

data Vec (a : Type) : (n : Na) → Type where
  Nil : Vec a Ze
  Cons : (x : a) (xs : Vec a n) → Vec a (Su n)

{-# COMPILE AGDA2HS Vec gadt #-}
