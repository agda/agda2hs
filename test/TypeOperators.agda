module TypeOperators where

{-# FOREIGN AGDA2HS {-# LANGUAGE TypeOperators #-} #-}

open import Haskell.Prim.Either

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

_:++:_ : Set → Set → Set
_:++:_ = Either
{-# COMPILE AGDA2HS _:++:_ #-}

mx : Bool :++: Nat
mx = Left true
{-# COMPILE AGDA2HS mx #-}

_++++_ : Set → Set → Set
_++++_ = Either
{-# COMPILE AGDA2HS _++++_ #-}

mx' : Bool ++++ Nat
mx' = Left true
{-# COMPILE AGDA2HS mx' #-}

data _****_ (a b : Set): Set where
  _:****_ : a → b → a **** b
{-# COMPILE AGDA2HS _****_ #-}

cross : Bool **** Nat
cross = true :**** 1
{-# COMPILE AGDA2HS cross #-}
