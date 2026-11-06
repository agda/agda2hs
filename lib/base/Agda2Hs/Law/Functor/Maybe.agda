module Agda2Hs.Law.Functor.Maybe where

open import Haskell.Prim
open import Haskell.Prim.Maybe

open import Haskell.Prim.Functor

open import Agda2Hs.Law.Functor.Def

instance
  iLawfulFunctorMaybe : IsLawfulFunctor Maybe
  iLawfulFunctorMaybe .identity = λ { Nothing → refl; (Just _) → refl }

  iLawfulFunctorMaybe .composition = λ { Nothing _ _ → refl; (Just _) _ _ → refl }
