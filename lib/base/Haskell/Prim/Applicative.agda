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


--------------------------------------------------------------------------------
-- Applicative

-- ** base
record Applicative (f : Type → Type) : Type₁ where
  infixl 4 _<*>_ _<*_ _*>_
  field
    pure   : a → f a
    _<*>_  : f (a → b) → f a → f b
    liftA2 : (a → b → c) → f a → f b → f c
    overlap ⦃ super ⦄ : Functor f
    _<*_ : f a → f b → f a
    _*>_ : f a → f b → f b

-- ** defaults
record ApplicativeFromLiftA2 (f : Type → Type) : Type₁ where
  constructor mk
  infixl 4 _<*>_ _<*_ _*>_
  field
    pure  : a → f a
    liftA2 : (a → b → c) → f a → f b → f c
    overlap ⦃ super ⦄ : Functor f

  _<*>_  : f (a → b) → f a → f b
  _<*>_ = liftA2 id

  _<*_ : f a → f b → f a
  _<*_ = liftA2 const

  _*>_ : f a → f b → f b
  x *> y = (id <$ x) <*> y

record ApplicativeFrom<*> (f : Type → Type) : Type₁ where
  constructor mk
  infixl 4 _<*>_ _<*_ _*>_
  field
    pure  : a → f a
    _<*>_ : f (a → b) → f a → f b
    overlap ⦃ super ⦄ : Functor f

  liftA2 : (a → b → c) → f a → f b → f c
  liftA2 f x y = fmap f x <*> y

  _<*_ : f a → f b → f a
  x <* y = fmap const x <*> y

  _*>_ : f a → f b → f b
  x *> y = fmap (const id) x <*> y

-- ** export
open Applicative ⦃...⦄ public
{-# COMPILE AGDA2HS Applicative existing-class #-}

-- ** instances
instance
  open ApplicativeFrom<*>

  iDefaultApplicativeList : ApplicativeFrom<*> List
  iDefaultApplicativeList .pure x = x ∷ []
  iDefaultApplicativeList ._<*>_ fs xs = foldMap (λ f → map f xs) fs

  iApplicativeList : Applicative List
  iApplicativeList = record {ApplicativeFrom<*> iDefaultApplicativeList}

  iDefaultApplicativeMaybe : ApplicativeFrom<*> Maybe
  iDefaultApplicativeMaybe .pure = Just
  iDefaultApplicativeMaybe ._<*>_ (Just f) (Just x) = Just (f x)
  iDefaultApplicativeMaybe ._<*>_ _        _        = Nothing

  iApplicativeMaybe : Applicative Maybe
  iApplicativeMaybe = record {ApplicativeFrom<*> iDefaultApplicativeMaybe}

  iDefaultApplicativeEither : ApplicativeFrom<*> (Either a)
  iDefaultApplicativeEither .pure = Right
  iDefaultApplicativeEither ._<*>_ (Right f) (Right x) = Right (f x)
  iDefaultApplicativeEither ._<*>_ (Left e)  _         = Left e
  iDefaultApplicativeEither ._<*>_ _         (Left e)  = Left e

  iApplicativeEither : Applicative (Either a)
  iApplicativeEither = record{ApplicativeFrom<*> iDefaultApplicativeEither}

  iDefaultApplicativeFun : ApplicativeFrom<*> (λ b → a → b)
  iDefaultApplicativeFun .pure        = const
  iDefaultApplicativeFun ._<*>_ f g x = f x (g x)

  iApplicativeFun : Applicative (λ b → a → b)
  iApplicativeFun = record{ApplicativeFrom<*> iDefaultApplicativeFun}

  iDefaultApplicativeTuple₂ : ⦃ Monoid a ⦄ → ApplicativeFrom<*> (a ×_)
  iDefaultApplicativeTuple₂ .pure x                = mempty , x
  iDefaultApplicativeTuple₂ ._<*>_ (a , f) (b , x) = a <> b , f x

  iApplicativeTuple₂ : ⦃ Monoid a ⦄ → Applicative (a ×_)
  iApplicativeTuple₂ = record{ApplicativeFrom<*> iDefaultApplicativeTuple₂}

  iDefaultApplicativeTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → ApplicativeFrom<*> (a × b ×_)
  iDefaultApplicativeTuple₃ .pure x = mempty , mempty , x
  iDefaultApplicativeTuple₃ ._<*>_ (a , u , f) (b , v , x) = a <> b , u <> v , f x

  iApplicativeTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → Applicative (a × b ×_)
  iApplicativeTuple₃ = record{ApplicativeFrom<*> iDefaultApplicativeTuple₃}

  iDefaultApplicativeIO : ApplicativeFrom<*> IO
  iDefaultApplicativeIO .pure = returnIO
  iDefaultApplicativeIO ._<*>_ m1 m2 = bindIO m1 (λ f → bindIO m2 (λ x → returnIO (f x)))

  iApplicativeIO : Applicative IO
  iApplicativeIO = record{ApplicativeFrom<*> iDefaultApplicativeIO}
