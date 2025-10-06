
-- | Postulates and definitions of the operations supported by 'Set'.
module Haskell.Data.Set where

open import Haskell.Prelude hiding (lookup; null; map; filter)

{-----------------------------------------------------------------------------
    Data.Set
------------------------------------------------------------------------------}

postulate
  Set : Type → Type

module _ {a : Type} where
  postulate
    toAscList : Set a → List a
    null      : Set a → Bool

module _ {a : Type} {{_ : Ord a}} where
  postulate
    member    : a → Set a → Bool

    empty     : Set a
    insert    : a → Set a → Set a
    delete    : a → Set a → Set a
    fromList  : List a → Set a

    map          : ∀ {b} {{_ : Ord b}} → (a → b) → Set a → Set b
    union        : Set a → Set a → Set a
    intersection : Set a → Set a → Set a
    difference   : Set a → Set a → Set a
    filter       : (a → Bool) → Set a → Set a

    isSubsetOf   : Set a → Set a → Bool

    prop-member-null
      : ∀ (s : Set a)
          (_ : ∀ (x : a) → member x s ≡ False)
      → null s ≡ True

    prop-null→empty
      : ∀ (s : Set a)
      → null s ≡ True
      → s ≡ empty

    prop-equality
      : ∀ {s1 s2 : Set a}
      → (∀ (x : a) → member x s1 ≡ member x s2)
      → s1 ≡ s2

    prop-member-empty
      : ∀ (x : a)
      → member x empty ≡ False

    prop-member-insert
      : ∀ (x xi : a) (s : Set a)
      → member x (insert xi s)
        ≡ (if (x == xi) then True else member x s)

    prop-member-delete
      : ∀ (x xi : a) (s : Set a)
      → member x (delete xi s)
        ≡ (if (x == xi) then False else member x s)

    prop-member-toAscList
      : ∀ (x : a) (s : Set a)
      → (elem x ∘ toAscList) s ≡ member x s

    prop-member-fromList
      : ∀ (x : a) (xs : List a)
      → member x (fromList xs)
        ≡ elem x xs

    prop-member-union
      : ∀ (x : a) (s1 s2 : Set a)
      → member x (union s1 s2)
        ≡ (member x s1 || member x s2)

    prop-member-intersection
      : ∀ (x : a) (s1 s2 : Set a)
      → member x (intersection s1 s2)
        ≡ (member x s1 && member x s2)

    prop-member-difference
      : ∀ (x : a) (s1 s2 : Set a)
      → member x (difference s1 s2)
        ≡ (member x s1 && not (member x s2))

    prop-member-filter
      : ∀ (x : a) (p : a → Bool) (s : Set a)
      → member x (filter p s)
        ≡ (p x && member x s)

    prop-isSubsetOf→intersection
      : ∀ (s1 s2 : Set a)
      → isSubsetOf s1 s2 ≡ True
      → intersection s1 s2 ≡ s1

    prop-intersection→isSubsetOf
      : ∀ (s1 s2 : Set a)
      → intersection s1 s2 ≡ s1
      → isSubsetOf s1 s2 ≡ True

  singleton : a → Set a
  singleton = λ x → insert x empty

  disjoint : Set a → Set a → Bool
  disjoint m = null ∘ intersection m

foldMap' : ∀ {{_ : Monoid b}} → (a → b) → Set a → b
foldMap' f = foldMap f ∘ toAscList

postulate
  prop-member-map
    : ∀ {a b} {{_ : Ord a}} {{_ : Ord b}}
      (x : a) (s : Set a) (f : a → b)
    → member (f x) (map f s) ≡ member x s

instance
  iSetFoldable : Foldable Set
  iSetFoldable =
    record {DefaultFoldable (record {foldMap = foldMap'})}

  iSetSemigroup : {{Ord a}} → Semigroup (Set a)
  iSetSemigroup ._<>_ = union

  iSetMonoid : {{Ord a}} → Monoid (Set a)
  iSetMonoid = record {DefaultMonoid (record {mempty = empty})}
