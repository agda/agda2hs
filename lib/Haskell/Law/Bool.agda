module Haskell.Law.Bool where

open import Haskell.Prim
open import Haskell.Prim.Bool

open import Haskell.Law.Equality

{-----------------------------------------------------------------------------
    Properties
    Logical operations and constants
------------------------------------------------------------------------------}
--
prop-x-&&-True
  : ∀ (x : Bool)
  → (x && True) ≡ x
--
prop-x-&&-True True = refl
prop-x-&&-True False = refl

--
prop-x-&&-False
  : ∀ (x : Bool)
  → (x && False) ≡ False
--
prop-x-&&-False True = refl
prop-x-&&-False False = refl

--
prop-x-||-True
  : ∀ (x : Bool)
  → (x || True) ≡ True
--
prop-x-||-True True = refl
prop-x-||-True False = refl

--
prop-x-||-False
  : ∀ (x : Bool)
  → (x || False) ≡ x
--
prop-x-||-False True = refl
prop-x-||-False False = refl

{-----------------------------------------------------------------------------
    Properties
    Boolean algebra
    https://en.wikipedia.org/wiki/Boolean_algebra_(structure)
------------------------------------------------------------------------------}
--
prop-||-idem
  : ∀ (a : Bool)
  → (a || a) ≡ a
--
prop-||-idem False = refl
prop-||-idem True = refl

--
prop-||-assoc
  : ∀ (a b c : Bool)
  → ((a || b) || c) ≡ (a || (b || c))
--
prop-||-assoc False b c = refl
prop-||-assoc True b c = refl

--
prop-||-sym
  : ∀ (a b : Bool)
  → (a || b) ≡ (b || a)
--
prop-||-sym False False = refl
prop-||-sym False True = refl
prop-||-sym True False = refl
prop-||-sym True True = refl

--
prop-||-absorb
  : ∀ (a b : Bool)
  → (a || (a && b)) ≡ a
--
prop-||-absorb False b = refl
prop-||-absorb True b = refl

--
prop-||-identity
  : ∀ (a : Bool)
  → (a || False) ≡ a
--
prop-||-identity False = refl
prop-||-identity True = refl

--
prop-||-&&-distribute
  : ∀ (a b c : Bool)
  → (a || (b && c)) ≡ ((a || b) && (a || c))
--
prop-||-&&-distribute False b c = refl
prop-||-&&-distribute True b c = refl

--
prop-||-complement
  : ∀ (a : Bool)
  → (a || not a) ≡ True
--
prop-||-complement False = refl
prop-||-complement True = refl

--
prop-&&-idem
  : ∀ (a : Bool)
  → (a && a) ≡ a
--
prop-&&-idem False = refl
prop-&&-idem True = refl

--
prop-&&-assoc
  : ∀ (a b c : Bool)
  → ((a && b) && c) ≡ (a && (b && c))
--
prop-&&-assoc False b c = refl
prop-&&-assoc True b c = refl

--
prop-&&-sym
  : ∀ (a b : Bool)
  → (a && b) ≡ (b && a)
--
prop-&&-sym False False = refl
prop-&&-sym False True = refl
prop-&&-sym True False = refl
prop-&&-sym True True = refl

--
prop-&&-absorb
  : ∀ (a b : Bool)
  → (a && (a || b)) ≡ a
--
prop-&&-absorb False b = refl
prop-&&-absorb True b = refl

--
prop-&&-identity
  : ∀ (a : Bool)
  → (a && True) ≡ a
--
prop-&&-identity False = refl
prop-&&-identity True = refl

--
prop-&&-||-distribute
  : ∀ (a b c : Bool)
  → (a && (b || c)) ≡ ((a && b) || (a && c))
--
prop-&&-||-distribute False b c = refl
prop-&&-||-distribute True b c = refl

--
prop-&&-complement
  : ∀ (a : Bool)
  → (a && not a) ≡ False
--
prop-&&-complement False = refl
prop-&&-complement True = refl

--
prop-deMorgan-not-&&
  : ∀ (a b : Bool)
  → not (a && b) ≡ (not a || not b)
--
prop-deMorgan-not-&& False b = refl
prop-deMorgan-not-&& True b = refl

--
prop-deMorgan-not-||
  : ∀ (a b : Bool)
  → not (a || b) ≡ (not a && not b)
--
prop-deMorgan-not-|| False b = refl
prop-deMorgan-not-|| True b = refl

{-----------------------------------------------------------------------------
    Properties
    Other
------------------------------------------------------------------------------}

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
&&-leftTrue' .True True True _ refl = refl

&&-rightTrue : ∀ (a b : Bool) → (a && b) ≡ True → b ≡ True
&&-rightTrue True True _ = refl

&&-rightTrue' : ∀ (a b c : Bool) → a ≡ (b && c) → a ≡ True → b ≡ True
&&-rightTrue' .True True True _ refl = refl

--------------------------------------------------
-- ||

-- if a then True else b

||-excludedMiddle : ∀ (a b : Bool) → (a || not a) ≡ True
||-excludedMiddle False _ = refl
||-excludedMiddle True  _ = refl

||-leftTrue : ∀ (a b : Bool) → a ≡ True → (a || b) ≡ True
||-leftTrue .True b refl = refl

||-rightTrue : ∀ (a b : Bool) → b ≡ True → (a || b) ≡ True
||-rightTrue False .True refl = refl
||-rightTrue True  .True refl = refl

--------------------------------------------------
-- not

not-not : ∀ (a : Bool) → not (not a) ≡ a
not-not False = refl
not-not True = refl

not-involution : ∀ (a b : Bool) → a ≡ not b → not a ≡ b
not-involution .(not b) b refl = not-not b

--------------------------------------------------
-- if_then_else_

ifFlip : ∀ (b)
       → (t : {{not b ≡ True}} → a)
       → (e : {{not b ≡ False}} → a)
       → (if not b then t                             else e) ≡
         (if b     then (e {{not-involution _ _ it}}) else t {{not-involution _ _ it}})
ifFlip False _ _ = refl
ifFlip True  _ _ = refl

ifTrueEqThen : ∀ (b : Bool)
             → {thn : {{b ≡ True}} → a}
             → {els : {{b ≡ False}} → a}
             → (pf : b ≡ True) → (if b then thn else els) ≡ thn {{pf}}
ifTrueEqThen .True refl = refl

ifFalseEqElse : ∀ (b : Bool)
             → {thn : {{b ≡ True}} → a}
             → {els : {{b ≡ False}} → a}
             → (pf : b ≡ False) → (if b then thn else els) ≡ els {{pf}}
ifFalseEqElse .False refl = refl
