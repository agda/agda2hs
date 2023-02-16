
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

open Foldable ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Foldable existing-class #-}

foldr : ⦃ Foldable t ⦄ → (a → b → b) → b → t a → b
foldr f z t = foldMap ⦃ it ⦄ ⦃ MonoidEndo ⦄ f t z

foldl : ⦃ Foldable t ⦄ → (b → a → b) → b → t a → b
foldl f z t = foldMap ⦃ it ⦄ ⦃ MonoidEndoᵒᵖ ⦄ (flip f) t z

any : ⦃ Foldable t ⦄ → (a → Bool) → t a → Bool
any = foldMap ⦃ it ⦄ ⦃ MonoidDisj ⦄

all : ⦃ Foldable t ⦄ → (a → Bool) → t a → Bool
all = foldMap ⦃ it ⦄ ⦃ MonoidConj ⦄

and : ⦃ Foldable t ⦄ → t Bool → Bool
and = all id

or : ⦃ Foldable t ⦄ → t Bool → Bool
or = any id

null : ⦃ Foldable t ⦄ → t a → Bool
null = all (const False)

concat : ⦃ Foldable t ⦄ → t (List a) → List a
concat = foldMap id

concatMap : ⦃ Foldable t ⦄ → (a → List b) → t a → List b
concatMap = foldMap

elem : ⦃ Foldable t ⦄ → ⦃ Eq a ⦄ → a → t a → Bool
elem x = foldMap ⦃ it ⦄ ⦃ MonoidDisj ⦄ (x ==_)

notElem : ⦃ Foldable t ⦄ → ⦃ Eq a ⦄ → a → t a → Bool
notElem x t = not (elem x t)

toList : ⦃ Foldable t ⦄ → t a → List a
toList = foldr _∷_ []

sum : ⦃ Foldable t ⦄ → ⦃ iNum : Num a ⦄ → t a → a
sum = foldMap ⦃ it ⦄ ⦃ MonoidSum ⦄ id

product : ⦃ Foldable t ⦄ → ⦃ iNum : Num a ⦄ → t a → a
product = foldMap ⦃ it ⦄ ⦃ MonoidProduct ⦄ id

length : ⦃ Foldable t ⦄ → t a → Int
length = foldMap ⦃ it ⦄ ⦃ MonoidSum ⦄ (const 1)

instance
  iFoldableList : Foldable List
  iFoldableList .foldMap = foldMapList
    where
      foldMapList : ⦃ Monoid b ⦄ → (a → b) → List a → b
      foldMapList f []       = mempty
      foldMapList f (x ∷ xs) = f x <> foldMapList f xs

  iFoldableMaybe : Foldable Maybe
  iFoldableMaybe .foldMap _ Nothing  = mempty
  iFoldableMaybe .foldMap f (Just x) = f x

  iFoldableEither : Foldable (Either a)
  iFoldableEither .foldMap _ (Left _) = mempty
  iFoldableEither .foldMap f (Right x) = f x

  iFoldablePair : Foldable (a ×_)
  iFoldablePair .foldMap f (_ , x) = f x
