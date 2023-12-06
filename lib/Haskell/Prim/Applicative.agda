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
  infixl 4 _<*>_
  field
    pure  : a → f a
    _<*>_ : f (a → b) → f a → f b
    overlap ⦃ super ⦄ : Functor f
    _<*_ : f a → f b → f a
    _*>_ : f a → f b → f b
-- ** defaults
record DefaultApplicative (f : Set → Set) : Set₁ where
  constructor mk
  infixl 4 _<*>_
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
private
  mkApplicative : DefaultApplicative t → Applicative t
  mkApplicative x = record {DefaultApplicative x}
instance
  open DefaultApplicative

  iApplicativeList : Applicative List
  iApplicativeList = mkApplicative λ where
    .pure x      → x ∷ []
    ._<*>_ fs xs → concatMap (λ f → map f xs) fs

  iApplicativeMaybe : Applicative Maybe
  iApplicativeMaybe = mkApplicative λ where
    .pure → Just
    ._<*>_ (Just f) (Just x) → Just (f x)
    ._<*>_ _        _        → Nothing

  iApplicativeEither : Applicative (Either a)
  iApplicativeEither = mkApplicative λ where
    .pure → Right
    ._<*>_ (Right f) (Right x) → Right (f x)
    ._<*>_ (Left e)  _         → Left e
    ._<*>_ _         (Left e)  → Left e

  iApplicativeFun : Applicative (λ b → a → b)
  iApplicativeFun = mkApplicative λ where
    .pure        → const
    ._<*>_ f g x → f x (g x)

  iApplicativeTuple₂ : ⦃ Monoid a ⦄ → Applicative (a ×_)
  iApplicativeTuple₂ = mkApplicative λ where
    .pure x                → mempty , x
    ._<*>_ (a , f) (b , x) → a <> b , f x

  iApplicativeTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → Applicative (a × b ×_)
  iApplicativeTuple₃ = mkApplicative λ where
    .pure x                → mempty , mempty , x
    ._<*>_ (a , u , f) (b , v , x) → a <> b , u <> v , f x

instance postulate iApplicativeIO : Applicative IO
