
module Haskell.Prim.Foldable where

open import Haskell.Prim
open import Haskell.Prim.Num
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

record Foldable (t : Set → Set) : Set₁ where
  field
    foldMap : ⦃ Monoid b ⦄ → (a → b) → t a → b

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
  null = all (const false)

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

open Foldable ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Foldable existing-class #-}

instance
  iFoldableList : Foldable List
  iFoldableList .foldMap f []       = mempty
  iFoldableList .foldMap f (x ∷ xs) = f x <> foldMap f xs

  iFoldableMaybe : Foldable Maybe
  iFoldableMaybe .foldMap _ Nothing  = mempty
  iFoldableMaybe .foldMap f (Just x) = f x

  iFoldableEither : Foldable (Either a)
  iFoldableEither .foldMap _ (Left _) = mempty
  iFoldableEither .foldMap f (Right x) = f x

  iFoldablePair : Foldable (a ×_)
  iFoldablePair .foldMap f (_ , x) = f x
