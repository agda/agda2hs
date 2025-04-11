{-# OPTIONS --erasure #-}

module Data.Map.Maybe
    {-
    This module adds functions for the 'Maybe' type
    that are analogous to the functions in 'Data.Map'.
    This is used to make proofs for 'Data.Map' more transparent.
    -} where

open import Haskell.Law.Equality
open import Haskell.Prelude hiding (null; map; filter)

open import Haskell.Data.Maybe using
    ( isJust
    )

{-----------------------------------------------------------------------------
    Data.Maybe
    Functions
------------------------------------------------------------------------------}

null : Maybe a → Bool
null Nothing = True
null (Just x) = False

update : (a → Maybe a) → Maybe a → Maybe a
update f Nothing = Nothing
update f (Just x) = f x

filter : (a → Bool) → Maybe a → Maybe a
filter p Nothing = Nothing
filter p (Just x) = if p x then Just x else Nothing

-- | Degenerate 'filter', does not look at the contents.
-- Similar to 'guard'.
filt : Bool → Maybe a → Maybe a
filt True m = m
filt False m = Nothing

mapMaybe : (a → Maybe b) → Maybe a → Maybe b
mapMaybe f Nothing = Nothing
mapMaybe f (Just x) = f x

unionWith : (a → a → a) → Maybe a → Maybe a → Maybe a
unionWith f Nothing my = my
unionWith f (Just x) Nothing = Just x
unionWith f (Just x) (Just y) = Just (f x y)

-- | Left-biased union.
union : Maybe a → Maybe a → Maybe a
union = unionWith (λ x y → x)

intersectionWith : (a → b → c) → Maybe a → Maybe b → Maybe c
intersectionWith f (Just x) (Just y) = Just (f x y)
intersectionWith _ _ _ = Nothing

disjoint : Maybe a → Maybe b → Bool
disjoint m = null ∘ intersectionWith const m

{-----------------------------------------------------------------------------
    Properties
    union
------------------------------------------------------------------------------}

--
prop-union-empty-right
  : ∀ {ma : Maybe a}
  → union ma Nothing ≡ ma
--
prop-union-empty-right {_} {Nothing} = refl
prop-union-empty-right {_} {Just x} = refl

-- | 'unionWith' is symmetric if we 'flip' the function.
-- Note that 'union' is left-biased, not symmetric.
--
prop-unionWith-sym
  : ∀ {f : a → a → a} {ma mb : Maybe a}
  → unionWith f ma mb ≡ unionWith (flip f) mb ma
--
prop-unionWith-sym {_} {f} {Nothing} {Nothing} = refl
prop-unionWith-sym {_} {f} {Just x}  {Nothing} = refl
prop-unionWith-sym {_} {f} {Nothing} {Just y} = refl
prop-unionWith-sym {_} {f} {Just x}  {Just y} = refl

--
prop-union-assoc
  : ∀ {ma mb mc : Maybe a}
  → union (union ma mb) mc ≡ union ma (union mb mc)
--
prop-union-assoc {_} {Nothing} {mb} {mc} = refl
prop-union-assoc {_} {Just x} {Nothing} {mc} = refl
prop-union-assoc {_} {Just x} {Just y} {Nothing} = refl
prop-union-assoc {_} {Just x} {Just y} {Just z} = refl

-- | 'union' is symmetric if at most one argument is 'Just'.
--
prop-union-sym
  : ∀ {ma mb : Maybe a}
  → disjoint ma mb ≡ True
  → union ma mb ≡ union mb ma
--
prop-union-sym {_} {Nothing} {Nothing} eq = refl
prop-union-sym {_} {Nothing} {Just x} eq = refl
prop-union-sym {_} {Just x} {Nothing} eq = refl

--
prop-union-left
  : ∀ (x : a) (mb : Maybe a)
  → union (Just x) mb ≡ Just x
--
prop-union-left x Nothing = refl
prop-union-left x (Just y) = refl

{-----------------------------------------------------------------------------
    Properties
    intersection
------------------------------------------------------------------------------}
--
prop-isJust-intersectionWith
  : ∀ {ma : Maybe a} {mb : Maybe b} {f : a → b → c}
  → isJust (intersectionWith f ma mb)
    ≡ (isJust ma && isJust mb)
--
prop-isJust-intersectionWith {_} {_} {_} {Nothing} = refl
prop-isJust-intersectionWith {_} {_} {_} {Just x} {Nothing} = refl
prop-isJust-intersectionWith {_} {_} {_} {Just x} {Just y} = refl

{-----------------------------------------------------------------------------
    Properties
    filter
------------------------------------------------------------------------------}
-- |
-- Since 'union' is left-biased,
-- filtering commutes with union if the predicate is constant.
--
-- If the predicate is not constant, there are counterexamples.
prop-filter-union
  : ∀ (p : a → Bool) {m1 m2 : Maybe a}
  → (∀ (x y : a) → p x ≡ p y)
  → filter p (union m1 m2)
    ≡ union (filter p m1) (filter p m2)
--
prop-filter-union p {Nothing} {m2} flat = refl
prop-filter-union p {Just x} {Nothing} flat
  with p x
... | True = refl
... | False = refl
prop-filter-union p {Just x} {Just y} flat
  rewrite flat x y
  with p y
... | True = refl
... | False = refl

--
@0 prop-filter-||
  : ∀ {ma : Maybe a} {p q : a → Bool}
  → filter (λ x → p x || q x) ma
    ≡ union (filter p ma) (filter q ma)
--
prop-filter-|| {_} {Nothing} {p} {q} = refl
prop-filter-|| {_} {Just x} {p} {q}
  with p x | q x
... | True  | True  = refl
... | True  | False = refl
... | False | True  = refl
... | False | False = refl

-- |
-- 'filt' is a special case of 'filter'.
prop-filter-filt
  : ∀ (b : Bool) (m : Maybe a)
  → filter (λ x → b) m
    ≡ filt b m
--
prop-filter-filt False Nothing = refl
prop-filter-filt True Nothing = refl
prop-filter-filt False (Just x) = refl
prop-filter-filt True (Just x) = refl

{-----------------------------------------------------------------------------
    Properties
    filt
------------------------------------------------------------------------------}
-- |
-- Since 'union' is left-biased,
-- filtering commutes with union if the predicate is constant.
--
-- If the predicate is not constant, there are counterexamples.
prop-filt-||
  : ∀ (x y : Bool) {m : Maybe a}
  → filt (x || y) m
    ≡ union (filt x m) (filt y m)
--
prop-filt-|| False y {Nothing} = refl
prop-filt-|| False y {Just x} = refl
prop-filt-|| True False {Nothing} = refl
prop-filt-|| True False {Just x} = refl
prop-filt-|| True True {Nothing} = refl
prop-filt-|| True True {Just x} = refl

--
prop-filt-union
  : ∀ (x : Bool) {m1 m2 : Maybe a}
  → filt x (union m1 m2)
    ≡ union (filt x m1) (filt x m2)
--
prop-filt-union False {Nothing} {m2} = refl
prop-filt-union True {Nothing} {m2} = refl
prop-filt-union False {Just y} {Nothing} = refl
prop-filt-union True {Just y} {Nothing} = refl
prop-filt-union False {Just y} {Just z} = refl
prop-filt-union True {Just y} {Just z} = refl

--
prop-filt-filt
  : ∀ (x y : Bool) (m : Maybe a)
  → filt x (filt y m) ≡ filt (x && y) m
--
prop-filt-filt False False m = refl
prop-filt-filt False True m = refl
prop-filt-filt True False m = refl
prop-filt-filt True True m = refl
