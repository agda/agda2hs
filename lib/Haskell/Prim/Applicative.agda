
module Haskell.Prim.Applicative where

open import Haskell.Prim
open import Haskell.Prim.Either
open import Haskell.Prim.Foldable
open import Haskell.Prim.Functor
open import Haskell.Prim.List
open import Haskell.Prim.Maybe
open import Haskell.Prim.Monoid
open import Haskell.Prim.Tuple


--------------------------------------------------
-- Applicative

record Applicative (f : Set → Set) : Set₁ where
  infixl 4 _<*>_
  field
    pure  : a → f a
    _<*>_ : f (a → b) → f a → f b
    overlap ⦃ super ⦄ : Functor f

  _<*_ : f a → f b → f a
  x <* y = const <$> x <*> y

  _*>_ : f a → f b → f b
  x *> y = const id <$> x <*> y

open Applicative ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Applicative existing-class #-}

instance
  iApplicativeList : Applicative List
  iApplicativeList .pure x      = x ∷ []
  iApplicativeList ._<*>_ fs xs = concatMap (λ f → map f xs) fs

  iApplicativeMaybe : Applicative Maybe
  iApplicativeMaybe .pure = Just
  iApplicativeMaybe ._<*>_ (Just f) (Just x) = Just (f x)
  iApplicativeMaybe ._<*>_ _        _        = Nothing

  iApplicativeEither : Applicative (Either a)
  iApplicativeEither .pure = Right
  iApplicativeEither ._<*>_ (Right f) (Right x) = Right (f x)
  iApplicativeEither ._<*>_ (Left e)  _         = Left e
  iApplicativeEither ._<*>_ _         (Left e)  = Left e

  iApplicativeFun : Applicative (λ b → a → b)
  iApplicativeFun .pure        = const
  iApplicativeFun ._<*>_ f g x = f x (g x)

  iApplicativeTuple₂ : ⦃ Monoid a ⦄ → Applicative (a ×_)
  iApplicativeTuple₂ .pure x                = mempty , x
  iApplicativeTuple₂ ._<*>_ (a , f) (b , x) = a <> b , f x

  iApplicativeTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → Applicative (a × b ×_)
  iApplicativeTuple₃ .pure x                          = mempty , mempty , x
  iApplicativeTuple₃ ._<*>_ (a , b , f) (a₁ , b₁ , x) = a <> a₁ , b <> b₁ , f x

  iApplicativeTuple₄ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → ⦃ Monoid c ⦄ →
                       Applicative (λ d → Tuple (a ∷ b ∷ c ∷ d ∷ []))
  iApplicativeTuple₄ .pure x                          = mempty ∷ mempty ∷ mempty ∷ x ∷ []
  iApplicativeTuple₄ ._<*>_ (a ∷ b ∷ c ∷ f ∷ []) (a₁ ∷ b₁ ∷ c₁ ∷ x ∷ []) =
    a <> a₁ ∷ b <> b₁ ∷ c <> c₁ ∷ f x ∷ []
