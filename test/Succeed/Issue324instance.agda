
open import Haskell.Prelude

instance
  eqBoolFun : Eq (Bool → Bool)
  eqBoolFun ._==_ x y = x True == y True && x False == y False

{-# COMPILE AGDA2HS eqBoolFun #-}

