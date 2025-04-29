
-- | Postulates and definitions of the operations supported by 'Map'.
module Haskell.Data.Map where

open import Haskell.Law.Equality
open import Haskell.Prelude hiding (lookup; null; map; filter)
import Haskell.Prelude as L using (map)

open import Haskell.Data.Maybe using
    ( isJust
    )

import Data.Map.Maybe as Maybe
import Haskell.Prelude as List using (map)

open import Data.Set using (Set)
import Data.Set as Set

{-----------------------------------------------------------------------------
    Helper predicates
------------------------------------------------------------------------------}
Antitonic : {a : Type} → {{Ord a}} → (a → Bool) → Type
Antitonic {a} p =
  ∀ {x y : a} → ((x <= y) ≡ True) → ((p x >= p y) ≡ True)

{-----------------------------------------------------------------------------
    Functions
    involving 1 value type
------------------------------------------------------------------------------}
postulate
  Map : ∀ (k : Type) → Type → Type

module _ {k a : Type} {{_ : Ord k}} where
  postulate
    lookup    : k → Map k a → Maybe a
    null      : Map k a → Bool
    toAscList : Map k a → List (k × a)

  member : k → Map k a → Bool
  member key = isJust ∘ lookup key

  elems : Map k a → List a
  elems = List.map snd ∘ toAscList

  keys : Map k a → List k
  keys = List.map fst ∘ toAscList

  keysSet : Map k a → Set k
  keysSet = Set.fromList ∘ keys

  size : Map k a → Int
  size = length ∘ toAscList

  postulate
    prop-elem-keys
      : ∀ (key : k) (m : Map k a)
      → elem key (keys m)
        ≡ member key m

  postulate
    empty     : Map k a
    insert    : k → a → Map k a → Map k a
    delete    : k → Map k a → Map k a
    update    : (a → Maybe a) → k → Map k a → Map k a
    fromList  : List (k × a) → Map k a
    fromListWith : (a → a → a) → List (k × a) → Map k a

    unionWith     : (a → a → a) → Map k a → Map k a → Map k a
    filterWithKey : (k → a → Bool) → Map k a → Map k a

    takeWhileAntitone : (k → Bool) → Map k a → Map k a
    dropWhileAntitone : (k → Bool) → Map k a → Map k a

    prop-lookup-null
      : ∀ (m : Map k a)
          (_ : ∀ (key : k) → lookup key m ≡ Nothing)
      → null m ≡ True

    prop-null→empty
      : ∀ (m : Map k a)
      → null m ≡ True
      → m ≡ empty
  
    prop-equality
      : ∀ {m1 m2 : Map k a}
      → (∀ (key : k) → lookup key m1 ≡ lookup key m2)
      → m1 ≡ m2

    prop-lookup-eq
      : ∀ (key1 key2 : k) (m : Map k a)
      → (key1 == key2) ≡ True
      → lookup key1 m ≡ lookup key2 m

    prop-lookup-empty
      : ∀ (key : k)
      → lookup key empty ≡ Nothing

    prop-lookup-insert
      : ∀ (key keyi : k) (x : a) (m : Map k a)
      → lookup key (insert keyi x m)
        ≡ (if (key == keyi) then Just x else lookup key m)

    prop-lookup-delete
      : ∀ (key keyi : k) (m : Map k a)
      → lookup key (delete keyi m)
        ≡ (if (key == keyi) then Nothing else lookup key m)

    prop-lookup-update
      : ∀ (key keyi : k) (m : Map k a) (f : a → Maybe a)
      → lookup key (update f keyi m)
        ≡ (if (key == keyi) then (lookup keyi m >>= f) else lookup key m)

    prop-lookup-unionWith
      : ∀ (key : k) (f : a → a → a) (m n : Map k a)
      → lookup key (unionWith f m n)
        ≡ Maybe.unionWith f (lookup key m) (lookup key n)

    prop-lookup-filterWithKey
      : ∀ (key : k) (m : Map k a) (p : k → a → Bool)
      → lookup key (filterWithKey p m)
        ≡ Maybe.filter (p key) (lookup key m)

    prop-lookup-takeWhileAntitone
      : ∀ (p : k → Bool) → Antitonic p
      → ∀ (key : k) (m : Map k a)
      → lookup key (takeWhileAntitone p m)
        ≡ lookup key (filterWithKey (λ k _ → p k) m)

    prop-lookup-dropWhileAntitone
      : ∀ (p : k → Bool) → Antitonic p
      → ∀ (key : k) (m : Map k a)
      → lookup key (dropWhileAntitone p m)
        ≡ lookup key (filterWithKey (λ k _ → not (p k)) m)


  singleton : k → a → Map k a
  singleton = λ k x → insert k x empty

  alter : (Maybe a → Maybe a) → k → Map k a → Map k a
  alter f k m = case f (lookup k m) of λ where
    Nothing → delete k m
    (Just a) → insert k a m

  insertWith : (a → a → a) → k → a → Map k a → Map k a
  insertWith f k new m = case lookup k m of λ where
    Nothing → insert k new m
    (Just old) → insert k (f new old) m

  withoutKeys : Map k a → Set k → Map k a
  withoutKeys m s = filterWithKey (λ k _ → not (Set.member k s)) m

  restrictKeys : Map k a → Set k → Map k a
  restrictKeys m s = filterWithKey (λ k _ → Set.member k s) m

  filter : (a → Bool) → Map k a → Map k a
  filter p = filterWithKey (λ _ x → p x)

  union : Map k a → Map k a → Map k a
  union = unionWith (λ x y → x)

  spanAntitone : (k → Bool) → Map k a → (Map k a × Map k a)
  spanAntitone p m = (takeWhileAntitone p m , dropWhileAntitone p m)

  foldMap' : ∀ {{_ : Monoid b}} → (a → b) → Map k a → b
  foldMap' f = foldMap f ∘ List.map snd ∘ toAscList

instance
  iMapFoldable : ∀ {k : Type} {{_ : Ord k}} → Foldable (Map k)
  iMapFoldable =
    record {DefaultFoldable (record {foldMap = foldMap'})}

instance
  iEqMap : ∀ {k v : Type} {{_ : Ord k}} {{_ : Eq v}} → Eq (Map k v)
  iEqMap ._==_ m1 m2 = toAscList m1 == toAscList m2

{-----------------------------------------------------------------------------
    Operations
    involving 2 value types
------------------------------------------------------------------------------}
module _ {k : Type} {{_ : Ord k}} where
  postulate
    instance
      iMapFunctor : Functor (Map k)    

module _ {k a b : Type} {{_ : Ord k}} where
  postulate

    mapWithKey : (k → a → b) → Map k a → Map k b
    mapMaybeWithKey : (k → a → Maybe b) → Map k a → Map k b

    intersection : Map k a → Map k b → Map k a

  map : (a → b) → Map k a → Map k b
  map = fmap

  disjoint : Map k a → Map k b → Bool
  disjoint m1 m2 = null (intersection m1 m2)

  postulate
    prop-lookup-fmap
      : ∀ (key : k) (m : Map k a) (f : a → b)
      → lookup key (fmap {{iMapFunctor}} f m)
        ≡ fmap f (lookup key m)

    prop-lookup-mapWithKey
      : ∀ (key : k) (m : Map k a) (f : k → a → b)
      → lookup key (mapWithKey f m)
        ≡ fmap (f key) (lookup key m)

    prop-lookup-mapMaybeWithKey
      : ∀ (key : k) (m : Map k a) (f : k → a → Maybe b)
      → lookup key (mapMaybeWithKey f m)
        ≡ Maybe.mapMaybe (f key) (lookup key m)

    prop-lookup-intersection
      : ∀ (key : k) (m1 : Map k a) (m2 : Map k b)
      → lookup key (intersection m1 m2)
        ≡ Maybe.intersectionWith const (lookup key m1) (lookup key m2)

{-----------------------------------------------------------------------------
    Operations
    involving 3 value types
------------------------------------------------------------------------------}
module _ {k a b c : Type} {{_ : Ord k}} where
  postulate

    intersectionWith : (a → b → c) → Map k a → Map k b → Map k c

    prop-lookup-intersectionWith
      : ∀ (key : k) (ma : Map k a) (mb : Map k b)
          (f : a → b → c)
      → lookup key (intersectionWith f ma mb)
        ≡ Maybe.intersectionWith f (lookup key ma) (lookup key mb)
