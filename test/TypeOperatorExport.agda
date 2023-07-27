module TypeOperatorExport where

{-# FOREIGN AGDA2HS {-# LANGUAGE TypeOperators #-} #-}

open import Agda.Primitive

_<_ : Set -> Set -> Set
a < b = a
{-# COMPILE AGDA2HS _<_ #-}

data _***_ {i j : Level} (a : Set i) (b : Set j) : Set (i ⊔ j) where
  _:*:_ : a -> b -> a *** b
open _***_ public
{-# COMPILE AGDA2HS _***_ #-}

open import Agda.Builtin.Bool

_&&&_ : Bool -> Bool -> Bool
false &&& _  = false
_     &&& b2 = b2
{-# COMPILE AGDA2HS _&&&_ #-}
