module Agda2Hs.Law.Functor.IO where

open import Haskell.Prim
open import Haskell.Prim.IO

open import Haskell.Prim.Functor

open import Agda2Hs.Law.Functor.Def

instance postulate isLawFulFunctorIO : IsLawfulFunctor IO
