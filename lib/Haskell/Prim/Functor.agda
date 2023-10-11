
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
  infixl 1 _<&>_
  infixl 4 _<$>_ _<$_ _$>_
  field
    fmap : (a → b) → f a → f b
    _<$>_ : (a → b) → f a → f b
    _<&>_ : f a → (a → b) → f b
    _<$_ : (@0 {{ b }} → a) → f b → f a
    _$>_ : f a → (@0 {{ a }} → b) → f b
    void : f a → f (Tuple [])
-- ** defaults
record DefaultFunctor (f : Set → Set) : Set₁ where
  field fmap : (a → b) → f a → f b

  infixl 1 _<&>_
  infixl 4 _<$>_ _<$_ _$>_

  _<$>_ : (a → b) → f a → f b
  _<$>_ = fmap

  _<&>_ : f a → (a → b) → f b
  m <&> f = fmap f m

  _<$_ : (@0 {{ b }} → a) → f b → f a
  x <$ m = fmap (λ b → x {{b}}) m

  _$>_ : f a → (@0 {{ a }} → b) → f b
  m $> x = x <$ m

  void : f a → f (Tuple [])
  void = tt <$_
-- ** export
open Functor ⦃...⦄ public
{-# COMPILE AGDA2HS Functor existing-class #-}
-- ** instances
private
  mkFunctor : DefaultFunctor t → Functor t
  mkFunctor x = record {DefaultFunctor x}

  fmap=_ : (∀ {a b} → (a → b) → f a → f b) → Functor f
  fmap= x = record {DefaultFunctor (record {fmap = x})}
instance
  iFunctorList : Functor List
  iFunctorList = fmap= map

  iFunctorMaybe : Functor Maybe
  iFunctorMaybe = fmap= λ where
    f Nothing  → Nothing
    f (Just x) → Just (f x)

  iFunctorEither : Functor (Either a)
  iFunctorEither = fmap= λ where
    f (Left  x) → Left x
    f (Right y) → Right (f y)

  iFunctorFun : Functor (λ b → a → b)
  iFunctorFun = fmap= _∘_

  iFunctorTuple₂ : Functor (a ×_)
  iFunctorTuple₂ = fmap= λ f (x , y) → x , f y

  iFunctorTuple₃ : Functor (a × b ×_)
  iFunctorTuple₃ = fmap= λ f (x , y , z) → x , y , f z

  iFunctorTuple₄ : Functor (λ d → Tuple (a ∷ b ∷ c ∷ d ∷ []))
  iFunctorTuple₄ = fmap= λ f (x ; y ; z ; w ; tt) → x ; y ; z ; f w ; tt

instance postulate iFunctiorIO : Functor IO
