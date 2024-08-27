module Haskell.Prim.Applicative where

open import Haskell.Prim
open import Haskell.Prim.Either
open import Haskell.Prim.Foldable
open import Haskell.Prim.Functor
open import Haskell.Prim.IO
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Monoid
open import Haskell.Prim.Tuple


--------------------------------------------------
-- Applicative

-- ** base
record Applicative (f : Set → Set) : Set₁ where
  infixl 4 _<*>_ _<*_ _*>_
  field
    pure  : a → f a
    _<*>_ : f (a → b) → f a → f b
    overlap ⦃ super ⦄ : Functor f
    _<*_ : f a → f b → f a
    _*>_ : f a → f b → f b
-- ** defaults
record DefaultApplicative (f : Set → Set) : Set₁ where
  constructor mk
  infixl 4 _<*>_ _<*_ _*>_
  field
    pure  : a → f a
    _<*>_ : f (a → b) → f a → f b
    overlap ⦃ super ⦄ : Functor f

  _<*_ : f a → f b → f a
  x <* y = const <$> x <*> y

  _*>_ : f a → f b → f b
  x *> y = const id <$> x <*> y
-- ** export
open Applicative ⦃...⦄ public
{-# COMPILE AGDA2HS Applicative existing-class #-}
-- ** instances
instance
  open DefaultApplicative

  iDefaultApplicativeList : DefaultApplicative List
  iDefaultApplicativeList .pure x = x ∷ []
  iDefaultApplicativeList ._<*>_ fs xs = concatMap (λ f → map f xs) fs

  iApplicativeList : Applicative List
  iApplicativeList = record {DefaultApplicative iDefaultApplicativeList}

  iDefaultApplicativeMaybe : DefaultApplicative Maybe
  iDefaultApplicativeMaybe .pure = Just
  iDefaultApplicativeMaybe ._<*>_ (Just f) (Just x) = Just (f x)
  iDefaultApplicativeMaybe ._<*>_ _        _        = Nothing

  iApplicativeMaybe : Applicative Maybe
  iApplicativeMaybe = record {DefaultApplicative iDefaultApplicativeMaybe}

  iDefaultApplicativeEither : DefaultApplicative (Either a)
  iDefaultApplicativeEither .pure = Right
  iDefaultApplicativeEither ._<*>_ (Right f) (Right x) = Right (f x)
  iDefaultApplicativeEither ._<*>_ (Left e)  _         = Left e
  iDefaultApplicativeEither ._<*>_ _         (Left e)  = Left e

  iApplicativeEither : Applicative (Either a)
  iApplicativeEither = record{DefaultApplicative iDefaultApplicativeEither}

  iDefaultApplicativeFun : DefaultApplicative (λ b → a → b)
  iDefaultApplicativeFun .pure        = const
  iDefaultApplicativeFun ._<*>_ f g x = f x (g x)

  iApplicativeFun : Applicative (λ b → a → b)
  iApplicativeFun = record{DefaultApplicative iDefaultApplicativeFun}

  iDefaultApplicativeTuple₂ : ⦃ Monoid a ⦄ → DefaultApplicative (a ×_)
  iDefaultApplicativeTuple₂ .pure x                = mempty , x
  iDefaultApplicativeTuple₂ ._<*>_ (a , f) (b , x) = a <> b , f x

  iApplicativeTuple₂ : ⦃ Monoid a ⦄ → Applicative (a ×_)
  iApplicativeTuple₂ = record{DefaultApplicative iDefaultApplicativeTuple₂}

  iDefaultApplicativeTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → DefaultApplicative (a × b ×_)
  iDefaultApplicativeTuple₃ .pure x = mempty , mempty , x
  iDefaultApplicativeTuple₃ ._<*>_ (a , u , f) (b , v , x) = a <> b , u <> v , f x

  iApplicativeTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → Applicative (a × b ×_)
  iApplicativeTuple₃ = record{DefaultApplicative iDefaultApplicativeTuple₃}

instance postulate iApplicativeIO : Applicative IO
