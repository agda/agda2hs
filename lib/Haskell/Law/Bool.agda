module Haskell.Law.Bool where

open import Haskell.Prim
open import Haskell.Prim.Bool

open import Haskell.Law.Equality

--------------------------------------------------
-- &&

&&-sym : ∀ (a b : Bool) → (a && b) ≡ (b && a)
&&-sym False False = refl
&&-sym False True = refl
&&-sym True False = refl
&&-sym True True = refl

&&-semantics : ∀ (a b : Bool) → a ≡ True → b ≡ True → (a && b) ≡ True
&&-semantics True True _ _ = refl

&&-leftAssoc : ∀ (a b c : Bool) → (a && b && c) ≡ True → ((a && b) && c) ≡ True
&&-leftAssoc True True True _ = refl

&&-leftAssoc' : ∀ (a b c : Bool) → (a && b && c) ≡ ((a && b) && c)
&&-leftAssoc' False b c = refl
&&-leftAssoc' True b c = refl

&&-leftTrue : ∀ (a b : Bool) → (a && b) ≡ True → a ≡ True
&&-leftTrue True True _ = refl

&&-leftTrue' : ∀ (a b c : Bool) → a ≡ (b && c) → a ≡ True → c ≡ True
&&-leftTrue' .True b c h refl rewrite &&-sym b c = &&-leftTrue c b (sym h)

&&-rightTrue : ∀ (a b : Bool) → (a && b) ≡ True → b ≡ True
&&-rightTrue True True _ = refl

&&-rightTrue' : ∀ (a b c : Bool) → a ≡ (b && c) → a ≡ True → b ≡ True
&&-rightTrue' .True b c h refl rewrite &&-sym b c = &&-rightTrue c b (sym h)

--------------------------------------------------
-- ||

-- if a then True else b

||-excludedMiddle : ∀ (a b : Bool) → (a || not a) ≡ True
||-excludedMiddle False _ = refl
||-excludedMiddle True  _ = refl

--------------------------------------------------
-- not

not-not : ∀ (a : Bool) → not (not a) ≡ a
not-not False = refl
not-not True = refl

not-binarity : ∀ (a b : Bool) → a ≡ not b → not a ≡ b
not-binarity .(not b) b refl = not-not b
