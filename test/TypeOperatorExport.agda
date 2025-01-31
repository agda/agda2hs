module TypeOperatorExport where

{-# FOREIGN AGDA2HS {-# LANGUAGE TypeOperators #-} #-}

open import Haskell.Prim

_<_ : Type -> Type -> Type
a < b = a
{-# COMPILE AGDA2HS _<_ #-}

data _***_ {i j : Level} (a : Type i) (b : Type j) : Type (i ⊔ j) where
  _:*:_ : a -> b -> a *** b
open _***_ public
{-# COMPILE AGDA2HS _***_ #-}

_&&&_ : Bool -> Bool -> Bool
False &&& _  = False
_     &&& b2 = b2
{-# COMPILE AGDA2HS _&&&_ #-}
