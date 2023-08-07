module Haskell.Law.Applicative.IO where

open import Haskell.Prim
open import Haskell.Prim.IO

open import Haskell.Prim.Applicative

open import Haskell.Law.Applicative.Def

open import Haskell.Law.Functor.IO

instance postulate iLawfulApplicativeIO : IsLawfulApplicative IO
