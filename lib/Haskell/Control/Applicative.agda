-- For some and many.
{-# OPTIONS --no-termination-check #-}

module Haskell.Control.Applicative where

open import Haskell.Prim
open import Haskell.Prim.Functor
open import Haskell.Prim.Applicative
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either

-- ** base
record Alternative (f : Set → Set) : Set₁ where
  infixl 3 _<|>_
  field
    empty  : f a
    _<|>_ : f a → f a → f a
    overlap ⦃ super ⦄ : Applicative f
    some : f a → f (List a)
    many : f a → f (List a)
-- ** defaults
record DefaultAlternative (f : Set → Set) : Set₁ where
  infixl 3 _<|>_
  field
    empty  : f a
    _<|>_ : f a → f a → f a
    overlap ⦃ super ⦄ : Applicative f

  -- | One or more.
  some many : f a -> f (List a)
  some v = _<*>_ (fmap _∷_ v) (many v)
  many v = some v <|> pure []

-- ** export
open Alternative ⦃...⦄ public
{-# COMPILE AGDA2HS Alternative existing-class #-}

-- ** functions
optional : {f : Set → Set} {{altf : Alternative f}} → f a → f (Maybe a)
optional v = Just <$> v <|> pure Nothing

-- ** instances
private
  mkAlternative : DefaultAlternative t → Alternative t
  mkAlternative x = record {DefaultAlternative x}
instance
  open DefaultAlternative

  iAlternativeMaybe : Alternative Maybe
  iAlternativeMaybe = mkAlternative λ where
    .empty → Nothing
    ._<|>_ Nothing m2 → m2
    ._<|>_ (Just a1) _ → Just a1
