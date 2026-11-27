
module Haskell.Prim.Functor where

open import Haskell.Prim
open import Haskell.Prim.Either
open import Haskell.Prim.IO
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Tuple


--------------------------------------------------------------------------------
-- Functor

-- ** base
record Functor (f : Type → Type) : Type₁ where
  infixl 4 _<$_
  field
    fmap : (a → b) → f a → f b
    _<$_ : (@0 {{ b }} → a) → f b → f a

-- ** defaults
record DefaultFunctor (f : Type → Type) : Type₁ where
  field fmap : (a → b) → f a → f b

  infixl 4 _<$_
  _<$_ : (@0 {{ b }} → a) → f b → f a
  x <$ m = fmap (λ b → x {{b}}) m

-- ** export
open Functor ⦃...⦄ public
{-# COMPILE AGDA2HS Functor existing-class #-}

-- ** instances
module Instances where
  instance
    open DefaultFunctor

    iDefaultFunctorList : DefaultFunctor List
    iDefaultFunctorList .fmap = map

    iFunctorList : Functor List
    iFunctorList = record{DefaultFunctor iDefaultFunctorList}

    iDefaultFunctorMaybe : DefaultFunctor Maybe
    iDefaultFunctorMaybe .fmap = λ where
      f Nothing  → Nothing
      f (Just x) → Just (f x)

    iFunctorMaybe : Functor Maybe
    iFunctorMaybe = record{DefaultFunctor iDefaultFunctorMaybe}

    iDefaultFunctorEither : DefaultFunctor (Either a)
    iDefaultFunctorEither .fmap = λ where
      f (Left  x) → Left x
      f (Right y) → Right (f y)

    iFunctorEither : Functor (Either a)
    iFunctorEither = record{DefaultFunctor iDefaultFunctorEither}

    iDefaultFunctorFun : DefaultFunctor (λ b → a → b)
    iDefaultFunctorFun .fmap = _∘_

    iFunctorFun : Functor (λ b → a → b)
    iFunctorFun = record{DefaultFunctor iDefaultFunctorFun}

    iDefaultFunctorTuple₂ : DefaultFunctor (a ×_)
    iDefaultFunctorTuple₂ .fmap = λ f (x , y) → x , f y

    iFunctorTuple₂ : Functor (a ×_)
    iFunctorTuple₂ = record{DefaultFunctor iDefaultFunctorTuple₂}

    iDefaultFunctorTuple₃ : DefaultFunctor (a × b ×_)
    iDefaultFunctorTuple₃ .fmap = λ where f (x , y , z) → x , y , f z

    iFunctorTuple₃ : Functor (a × b ×_)
    iFunctorTuple₃ = record{DefaultFunctor iDefaultFunctorTuple₃}

    iDefaultFunctorIO : DefaultFunctor IO
    iDefaultFunctorIO .fmap = λ f x → bindIO x (returnIO ∘ f)

    iFunctorIO : Functor IO
    iFunctorIO = record{DefaultFunctor iDefaultFunctorIO}
open Instances public
