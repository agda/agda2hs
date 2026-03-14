module Haskell.Prim.Foldable where

open import Haskell.Prim
open import Haskell.Prim.Num hiding (abs)
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord
open import Haskell.Prim.List
open import Haskell.Prim.Int
open import Haskell.Prim.Bool
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either
open import Haskell.Prim.Tuple
open import Haskell.Prim.Monoid


--------------------------------------------------------------------------------
-- Foldable

-- ** base
record Foldable (t : Type → Type) : Type₁ where
  field
    fold     : ⦃ Monoid b ⦄ → t b → b
    foldMap  : ⦃ Monoid b ⦄ → (a → b) → t a → b
    foldMap' : ⦃ Monoid b ⦄ → (a → b) → t a → b
    foldr    : (a → b → b) → b → t a → b
    foldr'   : (a → b → b) → b → t a → b
    foldl    : (b → a → b) → b → t a → b
    foldl'   : (b → a → b) → b → t a → b
    toList   : t a → List a
    foldr1   : (a → a → a) → (s : t a) → @0 ⦃ NonEmpty (toList s) ⦄ → a
    foldl1   : (a → a → a) → (s : t a) → @0 ⦃ NonEmpty (toList s) ⦄ → a
    null     : t a → Bool
    length   : t a → Int
    elem     : ⦃ Eq a ⦄ → a → t a → Bool
    maximum  : ⦃ Ord a ⦄ → (s : t a) → @0 ⦃ NonEmpty (toList s) ⦄ → a
    minimum  : ⦃ Ord a ⦄ → (s : t a) → @0 ⦃ NonEmpty (toList s) ⦄ → a
    sum      : ⦃ Num a ⦄ → t a → a
    product  : ⦃ Num a ⦄ → t a → a

-- ** defaults
record DefaultFoldable (t : Type → Type) : Type₁ where
  field foldMap : ⦃ Monoid b ⦄ → (a → b) → t a → b

  fold : ⦃ Monoid b ⦄ → t b → b
  fold = foldMap id

  foldr : (a → b → b) → b → t a → b
  foldr f z t = foldMap ⦃ MonoidEndo ⦄ f t z

  foldr' : (a → b → b) → b → t a → b
  foldr' = foldr

  foldl : (b → a → b) → b → t a → b
  foldl f z t = foldMap ⦃ MonoidEndoᵒᵖ ⦄ (flip f) t z

  foldl' : (b → a → b) → b → t a → b
  foldl' = foldl

  foldMap' : ⦃ Monoid b ⦄ → (a → b) → t a → b
  foldMap' f = foldl' (λ acc a → acc <> f a) mempty

  toList : t a → List a
  toList = foldr _∷_ []
  
  foldr1 : (a → a → a) → (s : t a) → @0 ⦃ NonEmpty (toList s) ⦄ → a
  foldr1 f s = let l = toList s
                   xs , x = init l , last l
               in foldrList f x xs
    where
      foldrList : (a → b → b) → b → List a → b
      foldrList f z = λ where
        []       → z
        (x ∷ xs) → f x (foldrList f z xs)

  foldl1 : (a → a → a) → (s : t a) → @0 ⦃ NonEmpty (toList s) ⦄ → a
  foldl1 f s with toList s
  ...           | x ∷ xs = foldlList f x xs
    where
      foldlList : (b → a → b) → b → List a → b
      foldlList f z = λ where
        []       → z
        (x ∷ xs) → foldlList f (f z x) xs
  
  null : t a → Bool
  null = foldMap ⦃ MonoidConj ⦄ (const False)
  
  length : t a → Int
  length = foldMap ⦃ MonoidSum ⦄ (const 1)
  
  elem : ⦃ Eq a ⦄ → a → t a → Bool
  elem x = foldMap ⦃ MonoidDisj ⦄ (x ==_)

  maximum : ⦃ Ord a ⦄ → (s : t a) → @0 ⦃ NonEmpty (toList s) ⦄ → a
  maximum = foldr1 max

  minimum : ⦃ Ord a ⦄ → (s : t a) → @0 ⦃ NonEmpty (toList s) ⦄ → a
  minimum = foldr1 min
  
  sum : ⦃ Num a ⦄ → t a → a
  sum = fold ⦃ MonoidSum ⦄
  
  product : ⦃ Num a ⦄ → t a → a
  product = fold ⦃ MonoidProduct ⦄

-- ** export
open Foldable ⦃...⦄ public
{-# COMPILE AGDA2HS Foldable existing-class #-}

-- ** instances
instance
  open DefaultFoldable

  iDefaultFoldableList : DefaultFoldable List
  iDefaultFoldableList .foldMap = foldMapList
    where
      foldMapList : ⦃ Monoid b ⦄ → (a → b) → List a → b
      foldMapList f []       = mempty
      foldMapList f (x ∷ xs) = f x <> foldMapList f xs

  iFoldableList : Foldable List
  iFoldableList = record {DefaultFoldable iDefaultFoldableList}

  iDefaultFoldableMaybe : DefaultFoldable Maybe
  iDefaultFoldableMaybe .foldMap = λ where
    _ Nothing  → mempty
    f (Just x) → f x

  iFoldableMaybe : Foldable Maybe
  iFoldableMaybe = record {DefaultFoldable iDefaultFoldableMaybe}

  iDefaultFoldableEither : DefaultFoldable (Either a)
  iDefaultFoldableEither .foldMap = λ where
    _ (Left _)  → mempty
    f (Right x) → f x

  iFoldableEither : Foldable (Either a)
  iFoldableEither = record {DefaultFoldable iDefaultFoldableEither}

  iDefaultFoldablePair : DefaultFoldable (a ×_)
  iDefaultFoldablePair .foldMap = λ f (_ , x) → f x

  iFoldablePair : Foldable (a ×_)
  iFoldablePair = record {DefaultFoldable iDefaultFoldablePair}
