
module Haskell.Prim.Functor where

open import Haskell.Prim
open import Haskell.Prim.Either
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Tuple

--------------------------------------------------
-- Functor

record Functor (f : Set → Set) : Set₁ where
  field
    fmap : (a → b) → f a → f b

  infixl 1 _<&>_
  infixl 4 _<$>_ _<$_ _$>_

  _<$>_ : (a → b) → f a → f b
  _<$>_ = fmap

  _<&>_ : f a → (a → b) → f b
  m <&> f = fmap f m

  _<$_ : a → f b → f a
  x <$ m = fmap (const x) m

  _$>_ : f a → b → f b
  m $> x = x <$ m

  void : f a → f (Tuple [])
  void = [] <$_

open Functor ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Functor existing-class #-}

instance
  iFunctorList : Functor List
  iFunctorList .fmap = map

  iFunctorMaybe : Functor Maybe
  iFunctorMaybe .fmap f Nothing  = Nothing
  iFunctorMaybe .fmap f (Just x) = Just (f x)

  iFunctorEither : Functor (Either a)
  iFunctorEither .fmap f (Left  x) = Left x
  iFunctorEither .fmap f (Right y) = Right (f y)

  iFunctorFun : Functor (λ b → a → b)
  iFunctorFun .fmap = _∘_

  iFunctorTuple₂ : Functor (a ×_)
  iFunctorTuple₂ .fmap f (x , y) = x , f y

  iFunctorTuple₃ : Functor (a × b ×_)
  iFunctorTuple₃ .fmap f (x , y , z) = x , y , f z

  iFunctorTuple₄ : Functor (λ d → Tuple (a ∷ b ∷ c ∷ d ∷ []))
  iFunctorTuple₄ .fmap f (x ∷ y ∷ z ∷ w ∷ []) = x ∷ y ∷ z ∷ f w ∷ []
