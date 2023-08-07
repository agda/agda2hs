module Haskell.Law.Functor.IO where

open import Haskell.Prim
open import Haskell.Prim.IO

open import Haskell.Prim.Functor

open import Haskell.Law.Functor.Def

instance postulate isLawFulFunctorIO : IsLawfulFunctor IO
