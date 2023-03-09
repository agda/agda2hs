
module Haskell.Prim.Foldable where

open import Haskell.Prim
open import Haskell.Prim.Num hiding (abs)
open import Haskell.Prim.Eq
open import Haskell.Prim.List
open import Haskell.Prim.Int
open import Haskell.Prim.Bool
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either
open import Haskell.Prim.Tuple
open import Haskell.Prim.Monoid

--------------------------------------------------
-- Foldable

-- ** base
record Foldable (t : Set → Set) : Set₁ where
  field
    foldMap : ⦃ Monoid b ⦄ → (a → b) → t a → b
    foldr : (a → b → b) → b → t a → b
    foldl : (b → a → b) → b → t a → b
    any : (a → Bool) → t a → Bool
    all : (a → Bool) → t a → Bool
    and : t Bool → Bool
    null : t a → Bool
    or : t Bool → Bool
    concat : t (List a) → List a
    concatMap : (a → List b) → t a → List b
    elem : ⦃ Eq a ⦄ → a → t a → Bool
    notElem : ⦃ Eq a ⦄ → a → t a → Bool
    toList : t a → List a
    sum : ⦃ iNum : Num a ⦄ → t a → a
    product : ⦃ iNum : Num a ⦄ → t a → a
    length : t a → Int
-- ** defaults
record DefaultFoldable (t : Set → Set) : Set₁ where
  module M = Foldable {t = t}
  field foldMap : ⦃ Monoid b ⦄ → (a → b) → t a → b

  foldr : (a → b → b) → b → t a → b
  foldr f z t = foldMap ⦃ MonoidEndo ⦄ f t z

  foldl : (b → a → b) → b → t a → b
  foldl f z t = foldMap ⦃ MonoidEndoᵒᵖ ⦄ (flip f) t z

  any : (a → Bool) → t a → Bool
  any = foldMap ⦃ MonoidDisj ⦄

  all : (a → Bool) → t a → Bool
  all = foldMap ⦃ MonoidConj ⦄

  and : t Bool → Bool
  and = all id

  or : t Bool → Bool
  or = any id

  null : t a → Bool
  null = all (const False)

  concat : t (List a) → List a
  concat = foldMap id

  concatMap : (a → List b) → t a → List b
  concatMap = foldMap

  elem : ⦃ Eq a ⦄ → a → t a → Bool
  elem x = foldMap ⦃ MonoidDisj ⦄ (x ==_)

  notElem : ⦃ Eq a ⦄ → a → t a → Bool
  notElem x t = not (elem x t)

  toList : t a → List a
  toList = foldr _∷_ []

  sum : ⦃ iNum : Num a ⦄ → t a → a
  sum = foldMap ⦃ MonoidSum ⦄ id

  product : ⦃ iNum : Num a ⦄ → t a → a
  product = foldMap ⦃ MonoidProduct ⦄ id

  length : t a → Int
  length = foldMap ⦃ MonoidSum ⦄ (const 1)
-- ** export
open Foldable ⦃...⦄ public
{-# COMPILE AGDA2HS Foldable existing-class #-}
-- ** instances
private
  mkFoldable : DefaultFoldable t → Foldable t
  mkFoldable x = record {DefaultFoldable x}

  foldMap=_ : (∀ {b a} → ⦃ Monoid b ⦄ → (a → b) → t a → b) → Foldable t
  foldMap= x = record {DefaultFoldable (record {foldMap = x})}
instance
  iFoldableList : Foldable List
  iFoldableList = foldMap= foldMapList
    where
      foldMapList : ⦃ Monoid b ⦄ → (a → b) → List a → b
      foldMapList f []       = mempty
      foldMapList f (x ∷ xs) = f x <> foldMapList f xs

  iFoldableMaybe : Foldable Maybe
  iFoldableMaybe = foldMap= λ where
    _ Nothing  → mempty
    f (Just x) → f x

  iFoldableEither : Foldable (Either a)
  iFoldableEither = foldMap= λ where
    _ (Left _)  → mempty
    f (Right x) → f x

  iFoldablePair : Foldable (a ×_)
  iFoldablePair = foldMap= λ f (_ , x) → f x
