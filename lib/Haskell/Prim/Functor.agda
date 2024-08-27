
module Haskell.Prim.Functor where

open import Haskell.Prim
open import Haskell.Prim.Either
open import Haskell.Prim.IO
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Tuple

--------------------------------------------------
-- Functor

-- ** base
record Functor (f : Set → Set) : Set₁ where
  infixl 4 _<$_
  field
    fmap : (a → b) → f a → f b
    _<$_ : (@0 {{ b }} → a) → f b → f a
-- ** defaults
record DefaultFunctor (f : Set → Set) : Set₁ where
  field fmap : (a → b) → f a → f b

  infixl 4 _<$_

  _<$_ : (@0 {{ b }} → a) → f b → f a
  x <$ m = fmap (λ b → x {{b}}) m

-- ** export
open Functor ⦃...⦄ public
{-# COMPILE AGDA2HS Functor existing-class #-}

_<$>_ : {{Functor f}} → (a → b) → f a → f b
_<$>_ = fmap

_<&>_ : {{Functor f}} → f a → (a → b) → f b
m <&> f = fmap f m

_$>_ : {{Functor f}} → f a → (@0 {{ a }} → b) → f b
m $> x = x <$ m

void : {{Functor f}} → f a → f ⊤
void = tt <$_

infixl 1 _<&>_
infixl 4 _<$>_ _$>_

instance
  iDefaultFunctorList : DefaultFunctor List
  iDefaultFunctorList .DefaultFunctor.fmap = map

  iFunctorList : Functor List
  iFunctorList = record{DefaultFunctor iDefaultFunctorList}

  iDefaultFunctorMaybe : DefaultFunctor Maybe
  iDefaultFunctorMaybe .DefaultFunctor.fmap = λ where
    f Nothing  → Nothing
    f (Just x) → Just (f x)

  iFunctorMaybe : Functor Maybe
  iFunctorMaybe = record{DefaultFunctor iDefaultFunctorMaybe}

  iDefaultFunctorEither : DefaultFunctor (Either a)
  iDefaultFunctorEither .DefaultFunctor.fmap = λ where
    f (Left  x) → Left x
    f (Right y) → Right (f y)

  iFunctorEither : Functor (Either a)
  iFunctorEither = record{DefaultFunctor iDefaultFunctorEither}

  iDefaultFunctorFun : DefaultFunctor (λ b → a → b)
  iDefaultFunctorFun .DefaultFunctor.fmap = _∘_

  iFunctorFun : Functor (λ b → a → b)
  iFunctorFun = record{DefaultFunctor iDefaultFunctorFun}

  iDefaultFunctorTuple₂ : DefaultFunctor (a ×_)
  iDefaultFunctorTuple₂ .DefaultFunctor.fmap = λ f (x , y) → x , f y

  iFunctorTuple₂ : Functor (a ×_)
  iFunctorTuple₂ = record{DefaultFunctor iDefaultFunctorTuple₂}

  iDefaultFunctorTuple₃ : DefaultFunctor (a × b ×_)
  iDefaultFunctorTuple₃ .DefaultFunctor.fmap = λ where f (x , y , z) → x , y , f z

  iFunctorTuple₃ : Functor (a × b ×_)
  iFunctorTuple₃ = record{DefaultFunctor iDefaultFunctorTuple₃}

instance postulate iFunctorIO : Functor IO
