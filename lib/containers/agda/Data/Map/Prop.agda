
-- | Proofs on 'Map'.
module Data.Map.Prop where

open import Haskell.Law.Bool
open import Haskell.Law.Equality
open import Haskell.Prelude hiding (lookup; null; map; filter)

open import Haskell.Data.Map
open import Haskell.Data.Maybe using
    ( isJust
    )

import Data.Map.Maybe as Maybe
import Haskell.Prelude as List using (map)
open import Data.Set using (Set)
import Data.Set as Set

{-----------------------------------------------------------------------------
    Proofs
    involving 1 value type
------------------------------------------------------------------------------}
module _ {k a : Type} {{_ : Ord k}} where

  --
  prop-member-null
    : ∀ (m : Map k a)
        (_ : ∀ (key : k) → member key m ≡ False)
    → null m ≡ True
  --
  prop-member-null m f = prop-lookup-null m (λ key → lem-isJust (f key))
    where
      lem-isJust
        : ∀ {x : Maybe a} → isJust x ≡ False → x ≡ Nothing
      lem-isJust {Nothing} refl = refl

  --
  prop-null-empty
    : null (empty {k} {a}) ≡ True
  --
  prop-null-empty =
    prop-member-null
      (empty {k} {a})
      (λ key → cong isJust (prop-lookup-empty key))

  --
  prop-lookup-singleton
    : ∀ (key keyi : k) (x : a)
    → lookup key (singleton keyi x)
      ≡ (if (key == keyi) then Just x else Nothing)
  --
  prop-lookup-singleton key keyi x =
    begin
      lookup key (singleton keyi x)
    ≡⟨⟩
      lookup key (insert keyi x empty)
    ≡⟨ prop-lookup-insert key keyi x empty ⟩
      (if (key == keyi) then Just x else lookup key empty)
    ≡⟨ cong (λ f → if (key == keyi) then Just x else f) (prop-lookup-empty key) ⟩
      (if (key == keyi) then Just x else Nothing)
    ∎

  --
  prop-lookup-union
    : ∀ (key : k) (m n : Map k a)
    → lookup key (union m n)
      ≡ Maybe.union (lookup key m) (lookup key n)
  --
  prop-lookup-union key m n = prop-lookup-unionWith key (λ x y → x) m n

  --
  prop-union-empty-left
    : ∀ {ma : Map k a}
    → union empty ma ≡ ma
  --
  prop-union-empty-left {ma} = prop-equality eq-key
    where
      eq-key = λ key →
        begin
          lookup key (union empty ma)
        ≡⟨ prop-lookup-union key empty ma ⟩
          Maybe.union (lookup key empty) (lookup key ma)
        ≡⟨ cong (λ o → Maybe.union o (lookup key ma)) (prop-lookup-empty key) ⟩
          Maybe.union Nothing (lookup key ma)
        ≡⟨⟩
          lookup key ma
        ∎

  --
  prop-union-empty-right
    : ∀ {ma : Map k a}
    → union ma empty ≡ ma
  --
  prop-union-empty-right {ma} = prop-equality eq-key
    where
      eq-key = λ key →
        begin
          lookup key (union ma empty)
        ≡⟨ prop-lookup-union key ma empty ⟩
          Maybe.union (lookup key ma) (lookup key empty)
        ≡⟨ cong (λ o → Maybe.union (lookup key ma) o) (prop-lookup-empty key) ⟩
          Maybe.union (lookup key ma) Nothing
        ≡⟨ Maybe.prop-union-empty-right ⟩
          lookup key ma
        ∎

  --
  prop-unionWith-sym
    : ∀ {f : a → a → a} {ma mb : Map k a}
    → unionWith f ma mb ≡ unionWith (flip f) mb ma
  --
  prop-unionWith-sym {f} {ma} {mb} = prop-equality eq-key
    where
      eq-key = λ key →
        begin
          lookup key (unionWith f ma mb)
        ≡⟨ prop-lookup-unionWith key f _ _ ⟩
          Maybe.unionWith f (lookup key ma) (lookup key mb)
        ≡⟨ Maybe.prop-unionWith-sym {_} {f} {lookup key ma} {lookup key mb} ⟩
          Maybe.unionWith (flip f) (lookup key mb) (lookup key ma)
        ≡⟨ sym (prop-lookup-unionWith key (flip f) _ _) ⟩
          lookup key (unionWith (flip f) mb ma)
        ∎

  --
  prop-union-sym
    : ∀ {ma mb : Map k a}
    → disjoint ma mb ≡ True
    → union ma mb ≡ union mb ma
  --
  prop-union-sym {ma} {mb} cond = prop-equality eq-key
    where
      lem1 : intersection ma mb ≡ empty
      lem1 = prop-null→empty (intersection ma mb) cond

      lem-disjoint = λ key →
        begin
          Maybe.disjoint (lookup key ma) (lookup key mb)
        ≡⟨⟩
          Maybe.null (Maybe.intersectionWith const (lookup key ma) (lookup key mb))
        ≡⟨ cong Maybe.null (sym (prop-lookup-intersection key ma mb)) ⟩
          Maybe.null (lookup key (intersection ma mb))
        ≡⟨ cong (λ o → Maybe.null (lookup key o)) lem1 ⟩
          Maybe.null (lookup key empty)
        ≡⟨ cong Maybe.null (prop-lookup-empty key) ⟩
          True
        ∎

      eq-key = λ key →
        begin
          lookup key (union ma mb)
        ≡⟨ prop-lookup-unionWith key const _ _ ⟩
          Maybe.union (lookup key ma) (lookup key mb)
        ≡⟨ Maybe.prop-union-sym {_} {lookup key ma} {lookup key mb} (lem-disjoint key) ⟩
          Maybe.union (lookup key mb) (lookup key ma)
        ≡⟨ sym (prop-lookup-unionWith key const _ _) ⟩
          lookup key (unionWith const mb ma)
        ∎

  --
  prop-union-assoc
    : ∀ {ma mb mc : Map k a}
    → union (union ma mb) mc ≡ union ma (union mb mc)
  --
  prop-union-assoc {ma} {mb} {mc} = prop-equality eq-key
    where
      eq-key = λ key →
        begin
          lookup key (union (union ma mb) mc)
        ≡⟨ prop-lookup-union key _ _ ⟩
          Maybe.union (lookup key (union ma mb)) (lookup key mc)
        ≡⟨ cong (λ o → Maybe.union o (lookup key mc)) (prop-lookup-union key _ _) ⟩
          Maybe.union (Maybe.union (lookup key ma) (lookup key mb)) (lookup key mc)
        ≡⟨ Maybe.prop-union-assoc {_} {lookup key ma} {_} {_} ⟩
          Maybe.union (lookup key ma) (Maybe.union (lookup key mb) (lookup key mc))
        ≡⟨ cong (λ o → Maybe.union (lookup key ma) o) (sym (prop-lookup-union key _ _)) ⟩
          Maybe.union (lookup key ma) (lookup key (union mb mc))
        ≡⟨ sym (prop-lookup-union key _ _) ⟩
          lookup key (union ma (union mb mc))
        ∎

  --
  prop-lookup-filter
    : ∀ (key : k) (m : Map k a) (p : a → Bool)
    → lookup key (filter p m)
      ≡ Maybe.filter p (lookup key m)
  --
  prop-lookup-filter key m p =
    prop-lookup-filterWithKey key m (λ _ x → p x)

  --
  prop-lookup-filterWithKey-Just
    : ∀ (key : k) (x : a) (m : Map k a) (p : k → a → Bool)
    → lookup key m ≡ Just x
    → lookup key (filterWithKey p m)
      ≡ (if p key x then Just x else Nothing)
  --
  prop-lookup-filterWithKey-Just key x m p eq =
    begin
      lookup key (filterWithKey p m)
    ≡⟨ prop-lookup-filterWithKey key m p ⟩
      Maybe.filter (p key) (lookup key m)
    ≡⟨ cong (Maybe.filter (p key)) eq ⟩
      Maybe.filter (p key) (Just x)
    ≡⟨⟩
      (if p key x then Just x else Nothing)
    ∎

{-----------------------------------------------------------------------------
    Proofs
    involving keysSet
------------------------------------------------------------------------------}
module _ {k a : Type} {{_ : Ord k}} where

  --
  prop-member-keysSet
    : ∀ {key : k} {m : Map k a}
    → Set.member key (keysSet m)
      ≡ member key m
  --
  prop-member-keysSet {key} {m} =
    begin
      Set.member key (keysSet m)
    ≡⟨ Set.prop-member-fromList key (keys m) ⟩
      elem key (keys m)
    ≡⟨ prop-elem-keys key m ⟩
      member key m
    ∎

  --
  prop-null-keysSet
    : ∀ {m : Map k a}
    → Set.null (keysSet m) ≡ null m
  --
  prop-null-keysSet {m}
    with null m in eql
    with Set.null (keysSet m) in eqr
  ... | True | True = refl
  ... | True | False = trans (sym eqr) lem2 -- contradiction
    where
      lem1 = λ key →
        begin
          Set.member key (keysSet m)
        ≡⟨ prop-member-keysSet ⟩
          member key m
        ≡⟨ cong (member key) (prop-null→empty m eql) ⟩
          member key empty
        ≡⟨ cong isJust (prop-lookup-empty key) ⟩
          False
        ∎
      lem2 = Set.prop-member-null (keysSet m) lem1
  ... | False | False = refl
  ... | False | True = sym (trans (sym eql) lem2) -- contradiction
    where
      lem1 = λ key →
        begin
          member key m
        ≡⟨ sym prop-member-keysSet ⟩
          Set.member key (keysSet m)
        ≡⟨ cong (Set.member key) (Set.prop-null→empty (keysSet m) eqr) ⟩
          Set.member key Set.empty
        ≡⟨ Set.prop-member-empty key ⟩
          False
        ∎
      lem2 = prop-member-null m lem1

  --
  prop-keysSet-empty
    : keysSet {k} {a} empty ≡ Set.empty {k}
  --
  prop-keysSet-empty =
      Set.prop-null→empty _ lem1
    where
      lem1 =
        begin
          Set.null (keysSet {k} {a} empty)
        ≡⟨ prop-null-keysSet ⟩
          null {k} {a} empty
        ≡⟨ prop-null-empty ⟩
          True
        ∎

  --
  prop-keysSet-intersection
      : ∀ {ma mb : Map k a}
      → keysSet (intersection ma mb)
        ≡ Set.intersection (keysSet ma) (keysSet mb)
  --
  prop-keysSet-intersection {ma} {mb} = Set.prop-equality lem1
    where
      lem1
        : ∀ (key : k)
        → Set.member key (keysSet (intersection ma mb))
          ≡ Set.member key (Set.intersection (keysSet ma) (keysSet mb))
      lem1 key =
        begin
          Set.member key (keysSet (intersection ma mb))
        ≡⟨ prop-member-keysSet ⟩
          member key (intersection ma mb)
        ≡⟨ cong isJust (prop-lookup-intersection _ _ _) ⟩
          isJust (Maybe.intersectionWith const (lookup key ma) (lookup key mb))
        ≡⟨ Maybe.prop-isJust-intersectionWith ⟩
          isJust (lookup key ma) && isJust (lookup key mb)
        ≡⟨⟩
          member key ma && member key mb
        ≡⟨ cong (λ o → o && _) (sym prop-member-keysSet) ⟩
          Set.member key (keysSet ma) && member key mb
        ≡⟨ cong (λ o → _ && o) (sym prop-member-keysSet) ⟩
          Set.member key (keysSet ma) && Set.member key (keysSet mb)
        ≡⟨ sym (Set.prop-member-intersection key (keysSet ma) (keysSet mb)) ⟩
          Set.member key (Set.intersection (keysSet ma) (keysSet mb))
        ∎

  --
  prop-keysSet-union
    : ∀ {ma mb : Map k a}
    → keysSet (union ma mb)
      ≡ Set.union (keysSet ma) (keysSet mb)
  --
  prop-keysSet-union {ma} {mb} = Set.prop-equality lem1
    where
      lem1
        : ∀ (key : k)
        → Set.member key (keysSet (union ma mb))
          ≡ Set.member key (Set.union (keysSet ma) (keysSet mb))
      lem1 key
        rewrite prop-member-keysSet {key} {union ma mb}
        | prop-lookup-union key ma mb
        | Set.prop-member-union {k} key (keysSet ma) (keysSet mb)
        | prop-member-keysSet {key} {ma}
        | prop-member-keysSet {key} {mb}
        with lookup key ma | lookup key mb
      ... | Nothing | Nothing = refl
      ... | Just a  | Nothing = refl
      ... | Nothing | Just b  = refl
      ... | Just a  | Just b  = refl

  --
  prop-disjoint-keysSet
    : ∀ {ma mb : Map k a}
    → disjoint ma mb
      ≡ Set.disjoint (keysSet ma) (keysSet mb)
  --
  prop-disjoint-keysSet {ma} {mb} =
    begin
      null (intersection ma mb)
    ≡⟨ sym prop-null-keysSet ⟩
      Set.null (keysSet (intersection ma mb))
    ≡⟨ cong Set.null prop-keysSet-intersection ⟩
      Set.null (Set.intersection (keysSet ma) (keysSet mb))
    ∎

{-----------------------------------------------------------------------------
    Proofs
    involving withoutKeys and restrictKeys
------------------------------------------------------------------------------}
module _ {k a : Type} {{_ : Ord k}} where

  --
  prop-lookup-withoutKeys
    : ∀ (key : k) (m : Map k a) (ks : Set k)
    → lookup key (withoutKeys m ks)
      ≡ Maybe.filt (not (Set.member key ks)) (lookup key m)
  --
  prop-lookup-withoutKeys key m ks =
      begin
        lookup key (withoutKeys m ks)
      ≡⟨ prop-lookup-filterWithKey key m p ⟩
        Maybe.filter (p key) (lookup key m)
      ≡⟨ Maybe.prop-filter-filt (not (Set.member key ks)) (lookup key m) ⟩
        Maybe.filt (not (Set.member key ks)) (lookup key m)
      ∎
    where
      p : k → a → Bool
      p = λ kx _ → not (Set.member kx ks)

  --
  prop-lookup-restrictKeys
    : ∀ (key : k) (m : Map k a) (ks : Set k)
    → lookup key (restrictKeys m ks)
      ≡ Maybe.filt (Set.member key ks) (lookup key m)
  --
  prop-lookup-restrictKeys key m ks =
      begin
        lookup key (restrictKeys m ks)
      ≡⟨ prop-lookup-filterWithKey key m p ⟩
        Maybe.filter (p key) (lookup key m)
      ≡⟨ Maybe.prop-filter-filt (Set.member key ks) (lookup key m) ⟩
        Maybe.filt (Set.member key ks) (lookup key m)
      ∎
    where
      p : k → a → Bool
      p = λ kx _ → Set.member kx ks

  --
  prop-withoutKeys-empty
    : ∀ (m : Map k a)
    → withoutKeys m Set.empty ≡ m
  --
  prop-withoutKeys-empty m = prop-equality eq-key
    where
      eq-key = λ key →
        begin
          lookup key (withoutKeys m Set.empty)
        ≡⟨ prop-lookup-withoutKeys key m Set.empty ⟩
          Maybe.filt (not (Set.member key Set.empty)) (lookup key m)
        ≡⟨ cong (λ o → Maybe.filt (not o) (lookup key m)) (Set.prop-member-empty key) ⟩
          Maybe.filt True (lookup key m)
        ≡⟨⟩
          lookup key m
        ∎

  --
  prop-withoutKeys-keysSet
    : ∀ (m : Map k a)
    → withoutKeys m (keysSet m) ≡ empty
  --
  prop-withoutKeys-keysSet m = prop-equality eq-key
    where
      ks = keysSet m

      lem1
        : ∀ (mx : Maybe a)
        → Maybe.filt (not (isJust mx)) mx ≡ Nothing
      lem1 Nothing = refl
      lem1 (Just x) = refl

      eq-key = λ key →
        begin
          lookup key (withoutKeys m ks)
        ≡⟨ prop-lookup-withoutKeys key m ks ⟩
          Maybe.filt (not (Set.member key ks)) (lookup key m)
        ≡⟨ cong (λ o → Maybe.filt (not o) (lookup key m)) prop-member-keysSet ⟩
          Maybe.filt (not (isJust (lookup key m))) (lookup key m)
        ≡⟨ lem1 (lookup key m) ⟩
          Nothing
        ≡⟨ sym (prop-lookup-empty key) ⟩
          lookup key empty
        ∎

  --
  prop-restrictKeys-union
    : ∀ (ma mb : Map k a) (ks : Set k)
    → restrictKeys (union ma mb) ks
      ≡ union (restrictKeys ma ks) (restrictKeys mb ks)
  --
  prop-restrictKeys-union ma mb ks = prop-equality eq-key
    where
      eq-key = λ key → let p = Set.member key ks in
        begin
          lookup key (restrictKeys (union ma mb) ks)
        ≡⟨ prop-lookup-restrictKeys key (union ma mb) ks ⟩
          Maybe.filt p (lookup key (union ma mb))
        ≡⟨ cong (Maybe.filt p) (prop-lookup-union key ma mb)  ⟩
          Maybe.filt p
            (Maybe.union (lookup key ma) (lookup key mb))
        ≡⟨ Maybe.prop-filt-union p {lookup key ma} {lookup key mb} ⟩
          Maybe.union
            (Maybe.filt p (lookup key ma))
            (Maybe.filt p (lookup key mb))
        ≡⟨ cong (λ o → Maybe.union o (Maybe.filt p (lookup key mb))) (sym (prop-lookup-restrictKeys key ma ks)) ⟩
          Maybe.union
            (lookup key (restrictKeys ma ks))
            (Maybe.filt p (lookup key mb))
        ≡⟨ cong (λ o → Maybe.union (lookup key (restrictKeys ma ks)) o) (sym (prop-lookup-restrictKeys key mb ks)) ⟩
          Maybe.union
            (lookup key (restrictKeys ma ks))
            (lookup key (restrictKeys mb ks))
        ≡⟨ sym (prop-lookup-union key _ _) ⟩
          lookup key (union (restrictKeys ma ks) (restrictKeys mb ks))
        ∎

  --
  prop-restrictKeys-keysSet
    : ∀ (m : Map k a)
    → restrictKeys m (keysSet m) ≡ m
  --
  prop-restrictKeys-keysSet m = prop-equality eq-key
    where
      ks = keysSet m

      lem1
        : ∀ (mx : Maybe a)
        → Maybe.filt (isJust mx) mx ≡ mx
      lem1 Nothing = refl
      lem1 (Just x) = refl

      eq-key = λ key →
        begin
          lookup key (restrictKeys m ks)
        ≡⟨ prop-lookup-restrictKeys key m ks ⟩
          Maybe.filt (Set.member key ks) (lookup key m)
        ≡⟨ cong (λ o → Maybe.filt o (lookup key m)) prop-member-keysSet ⟩
          Maybe.filt (isJust (lookup key m)) (lookup key m)
        ≡⟨ lem1 (lookup key m) ⟩
          lookup key m
        ∎

  --
  prop-withoutKeys-union
    : ∀ (ma mb : Map k a) (ks : Set k)
    → withoutKeys (union ma mb) ks
      ≡ union (withoutKeys ma ks) (withoutKeys mb ks)
  --
  prop-withoutKeys-union ma mb ks = prop-equality eq-key
    where
      eq-key = λ key → let p = not (Set.member key ks) in
        begin
          lookup key (withoutKeys (union ma mb) ks)
        ≡⟨ prop-lookup-withoutKeys key (union ma mb) ks ⟩
          Maybe.filt p (lookup key (union ma mb))
        ≡⟨ cong (Maybe.filt p) (prop-lookup-union key ma mb)  ⟩
          Maybe.filt p
            (Maybe.union (lookup key ma) (lookup key mb))
        ≡⟨ Maybe.prop-filt-union p {lookup key ma} {lookup key mb} ⟩
          Maybe.union
            (Maybe.filt p (lookup key ma))
            (Maybe.filt p (lookup key mb))
        ≡⟨ cong (λ o → Maybe.union o (Maybe.filt p (lookup key mb))) (sym (prop-lookup-withoutKeys key ma ks)) ⟩
          Maybe.union
            (lookup key (withoutKeys ma ks))
            (Maybe.filt p (lookup key mb))
        ≡⟨ cong (λ o → Maybe.union (lookup key (withoutKeys ma ks)) o) (sym (prop-lookup-withoutKeys key mb ks)) ⟩
          Maybe.union
            (lookup key (withoutKeys ma ks))
            (lookup key (withoutKeys mb ks))
        ≡⟨ sym (prop-lookup-union key _ _) ⟩
          lookup key (union (withoutKeys ma ks) (withoutKeys mb ks))
        ∎

  --
  prop-withoutKeys-difference
    : ∀ (m : Map k a) (ka kb : Set k)
    → withoutKeys m (Set.difference ka kb)
      ≡ union (withoutKeys m ka) (restrictKeys m kb)
  --
  prop-withoutKeys-difference m ka kb = prop-equality eq-key
    where
      eq-key
        : ∀ (key : k)
        → lookup key (withoutKeys m (Set.difference ka kb))
          ≡ lookup key (union (withoutKeys m ka) (restrictKeys m kb))
      eq-key key =
        begin
          lookup key (withoutKeys m (Set.difference ka kb))
        ≡⟨ prop-lookup-withoutKeys key _ (Set.difference ka kb) ⟩
          Maybe.filt pab (lookup key m)
        ≡⟨ cong (λ o → Maybe.filt o (lookup key m)) lem-pab ⟩
          Maybe.filt (pa || not-pb) (lookup key m)
        ≡⟨ Maybe.prop-filt-|| pa not-pb {lookup key m} ⟩
          Maybe.union
            (Maybe.filt pa (lookup key m))
            (Maybe.filt not-pb (lookup key m))
        ≡⟨ cong (λ o → Maybe.union o (Maybe.filt not-pb (lookup key m))) (sym (prop-lookup-withoutKeys key m ka)) ⟩
          Maybe.union
            (lookup key (withoutKeys m ka))
            (Maybe.filt not-pb (lookup key m))
        ≡⟨ cong (λ o → Maybe.union (lookup key (withoutKeys m ka)) o) (sym (prop-lookup-restrictKeys key m kb)) ⟩
          Maybe.union
            (lookup key (withoutKeys m ka))
            (lookup key (restrictKeys m kb))
        ≡⟨ sym (prop-lookup-union key _ _) ⟩
          lookup key (union (withoutKeys m ka) (restrictKeys m kb))
        ∎
        where
          pa = not (Set.member key ka)
          not-pb = Set.member key kb
          pab = not (Set.member key (Set.difference ka kb))

          lem-pab : pab ≡ (pa || not-pb)
          lem-pab =
            begin
              not (Set.member key (Set.difference ka kb))
            ≡⟨ cong not (Set.prop-member-difference key ka kb) ⟩
              not (Set.member key ka && not (Set.member key kb))
            ≡⟨ prop-deMorgan-not-&& (Set.member key ka) (not (Set.member key kb)) ⟩
              (not (Set.member key ka) || not (not (Set.member key kb)))
            ≡⟨ cong (λ o → not (Set.member key ka) || o) (not-not (Set.member key kb)) ⟩
              (not (Set.member key ka) || Set.member key kb)
            ∎

  --
  prop-withoutKeys-withoutKeys
    : ∀ (m : Map k a) (ka kb : Set k)
    → withoutKeys (withoutKeys m ka) kb
      ≡ withoutKeys m (Set.union ka kb)
  --
  prop-withoutKeys-withoutKeys m ka kb = prop-equality eq-key
    where
      eq-key
        : ∀ (key : k)
        → lookup key (withoutKeys (withoutKeys m ka) kb)
          ≡ lookup key (withoutKeys m (Set.union ka kb))
      eq-key key =
        begin
          lookup key (withoutKeys (withoutKeys m ka) kb)
        ≡⟨ prop-lookup-withoutKeys key _ kb ⟩
          Maybe.filt pb (lookup key (withoutKeys m ka))
        ≡⟨ cong (Maybe.filt pb) (prop-lookup-withoutKeys key _ ka) ⟩
          Maybe.filt pb (Maybe.filt pa (lookup key m))
        ≡⟨ Maybe.prop-filt-filt pb pa (lookup key m) ⟩
          Maybe.filt (pb && pa) (lookup key m)
        ≡⟨ cong (λ o → Maybe.filt o (lookup key m)) (sym lem-pab) ⟩
          Maybe.filt pab (lookup key m)
        ≡⟨ sym (prop-lookup-withoutKeys key _ (Set.union ka kb)) ⟩
          lookup key (withoutKeys m (Set.union ka kb))
        ∎
        where
          pa = not (Set.member key ka)
          pb = not (Set.member key kb)
          pab = not (Set.member key (Set.union ka kb))

          lem-pab : pab ≡ (pb && pa)
          lem-pab =
            begin
              not (Set.member key (Set.union ka kb))
            ≡⟨ cong not (Set.prop-member-union key ka kb) ⟩
              not (Set.member key ka || Set.member key kb)
            ≡⟨ prop-deMorgan-not-|| (Set.member key ka) (Set.member key kb) ⟩
              (not (Set.member key ka) && not (Set.member key kb))
            ≡⟨ &&-sym (not (Set.member key ka)) (not (Set.member key kb)) ⟩
              (not (Set.member key kb) && not (Set.member key ka))
            ∎

  --
  @0 prop-withoutKeys-intersection
    : ∀ (m : Map k a) (ka kb : Set k)
    → withoutKeys m (Set.intersection ka kb)
      ≡ union (withoutKeys m ka) (withoutKeys m kb)
  --
  prop-withoutKeys-intersection m ka kb = prop-equality eq-key
    where
      eq-key
        : ∀ (key : k)
        → lookup key (withoutKeys m (Set.intersection ka kb))
          ≡ lookup key (union (withoutKeys m ka) (withoutKeys m kb))
      eq-key key =
        begin
          lookup key (withoutKeys m (Set.intersection ka kb))
        ≡⟨ prop-lookup-withoutKeys key m (Set.intersection ka kb) ⟩
          Maybe.filt pab (lookup key m)
        ≡⟨ cong (λ o → Maybe.filt o (lookup key m)) lem-pab ⟩
          Maybe.filt (pa || pb) (lookup key m)
        ≡⟨ Maybe.prop-filt-|| pa pb {lookup key m} ⟩
          Maybe.union
            (Maybe.filt pa (lookup key m))
            (Maybe.filt pb (lookup key m))
        ≡⟨ cong (λ o → Maybe.union o (Maybe.filt pb (lookup key m))) (sym (prop-lookup-withoutKeys key m ka)) ⟩
          Maybe.union
            (lookup key (withoutKeys m ka))
            (Maybe.filt pb (lookup key m))
        ≡⟨ cong (λ o → Maybe.union (lookup key (withoutKeys m ka)) o) (sym (prop-lookup-withoutKeys key m kb)) ⟩
          Maybe.union
            (lookup key (withoutKeys m ka))
            (lookup key (withoutKeys m kb))
        ≡⟨ sym (prop-lookup-union key _ _) ⟩
          lookup key (union (withoutKeys m ka) (withoutKeys m kb))
        ∎
        where
          pa = not (Set.member key ka)
          pb = not (Set.member key kb)
          pab = not (Set.member key (Set.intersection ka kb))

          lem-pab : pab ≡ (pa || pb)
          lem-pab =
            begin
              not (Set.member key (Set.intersection ka kb))
            ≡⟨ cong not (Set.prop-member-intersection key ka kb) ⟩
              not (Set.member key ka && Set.member key kb)
            ≡⟨ prop-deMorgan-not-&& (Set.member key ka) (Set.member key kb) ⟩
              (not (Set.member key ka) || not (Set.member key kb))
            ∎

  --
  prop-union-restrictKeys-absorbs
    : ∀ (ma mb : Map k a)
    → union ma (restrictKeys mb (keysSet ma))
      ≡ ma
  --
  prop-union-restrictKeys-absorbs ma mb = prop-equality eq-key
    where
      eq-key
        : ∀ (key : k)
        → lookup key (union ma (restrictKeys mb (keysSet ma)))
          ≡ lookup key ma
      eq-key key
        rewrite prop-lookup-union key ma (restrictKeys mb (keysSet ma))
        | prop-lookup-restrictKeys key mb (keysSet ma)
        | prop-member-keysSet {k} {a} {key} {ma}
        with lookup key ma
      ... | Nothing = refl
      ... | Just a
          with lookup key mb
      ...   | Just b = refl
      ...   | Nothing = refl
