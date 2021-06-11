{-# OPTIONS --no-auto-inline #-}
module DefaultMethods where

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat using (Nat)
import Agda.Builtin.Nat as Nat
open import Agda.Builtin.List
open import Agda.Builtin.String renaming (primStringAppend to _++_)
open import Agda.Builtin.Char
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Maybe
open import Haskell.Prim.Foldable

-- open import Haskell.Prelude hiding (Show; showsPrec; )

-- ** Ord

record Ord (a : Set) : Set where
  field
    _<_ _>_ : a → a → Bool

record Ord₁ (a : Set) : Set where
  field
    _<_ : a → a → Bool

  _>_ : a → a → Bool
  x > y = y < x

record Ord₂ (a : Set) : Set where
  field
    _>_ : a → a → Bool

  _<_ : a → a → Bool
  _<_ = flip _>_

open Ord ⦃ ... ⦄

{-# COMPILE AGDA2HS Ord class Ord₁ Ord₂ #-}
-- CHECKS

-- instance
--   OrdBool₁ : Ord Bool
--   OrdBool₁ = record {Ord₁ (λ where .Ord₁._<_ → _<ᵇ_)}
--     where
--       _<ᵇ_ : Bool → Bool → Bool
--       false <ᵇ b = b
--       true  <ᵇ _ = false

--   -- OrdBool₂ : Ord Bool
--   -- OrdBool₂ = record {Ord₂ (λ where
--   --   .Ord₂._>_ false false → false
--   --   .Ord₂._>_ false true  → false
--   --   .Ord₂._>_ true  false → true
--   --   .Ord₂._>_ true  true  → false)}

--   Ordℕ : Ord Nat
--   Ordℕ = record {Ord₁ (λ where .Ord₁._<_ → Nat._<_)}
-- --   --   ~ record {_<_ = Ordℕ₁._<_; _>_ = Ordℕ₁._>_}
-- --   --   ~ OrdN ._<_ = OrdN1._<_       ~> compile N1._<_ (primitive)
-- --   --     OrdN ._>_ = OrdN1._>_       ~> drop N1._>_ (derived)
-- --   --   ~ record {_<_ = Ordℕ₁._<_; _>_ = λ ....}
-- --   --   ~ OrdN ._<_ = OrdN1._<_       ~> compile N1._<_ (primitive)
-- --   --     OrdN ._>_ = λ ....          ~> compile λ .... (not even related to N1)
-- {-# COMPILE AGDA2HS OrdBool₁ #-}
-- {-# COMPILE AGDA2HS Ordℕ #-}

ShowS : Set
ShowS = String → String
{-# COMPILE AGDA2HS ShowS #-}

showString : String → ShowS
showString = _++_
{-# COMPILE AGDA2HS showString #-}

showParen : Bool → ShowS → ShowS
showParen false s = s
showParen true  s = showString "(" ∘ s ∘ showString ")"
{-# COMPILE AGDA2HS showParen #-}

defaultShowList : (a → ShowS) → List a → ShowS
defaultShowList _     []       = showString "[]"
defaultShowList shows (x ∷ xs) = showString "[" ∘ foldl (λ s x → s ∘ showString "," ∘ shows x) (shows x) xs ∘ showString "]"
{-# COMPILE AGDA2HS defaultShowList #-}

record Show (a : Set) : Set where
  field
    show : a → String
    showPrec : Nat → a → ShowS
    showList : List a → ShowS

record Show₁ (a : Set) : Set where
  field
    showPrec : Nat → a → ShowS

  show : a → String
  show x = showPrec 0 x ""

  showList : List a → ShowS
  showList = defaultShowList (showPrec 0)

record Show₂ (a : Set) : Set where
  field
    show : a → String

  showPrec : Nat → a → ShowS
  showPrec _ x s = show x ++ s

  showList : List a → ShowS
  showList = defaultShowList (showPrec 0)

open Show ⦃ ... ⦄

{-# COMPILE AGDA2HS Show class Show₁ Show₂ #-}

-- -- NB: after looking up the minimal records, we can generate a GHC pragma {-# MINIMAL show | showPrec #-}
-- --    ++ overlapping definitions match (syntactically, after compiling Haskell!)
-- {- OUTPUT
-- class Show a where
--   show :: a → String
--   showPrec :: Int → a → ShowS
--   showList :: List a → ShowS

--   showPrec _ x s = show x ++ s
--   show x = showPrec 0 x ""
--   showList = defaultShowList (showPrec 0)
-- -}

-- SB : Show₂ Bool
-- SB .Show₂.show true  = "true"
-- SB .Show₂.show false = "false"

-- instance
--   ShowBool : Show Bool
--   ShowBool .show     = Show₂.show SB
--   ShowBool .showPrec = Show₂.showPrec SB
--   ShowBool .showList []       = showString ""
--   ShowBool .showList (true ∷ bs) = showString "1" ∘ showList bs
--   ShowBool .showList (false ∷ bs) = showString "0" ∘ showList bs

--   ShowMaybe : ⦃ Show a ⦄ → Show (Maybe a)
--   ShowMaybe {a = a} = record {Show₁ s₁}
--     where
--       s₁ : Show₁ (Maybe a)
--       s₁ .Show₁.showPrec n Nothing = showString "nothing"
--       s₁ .Show₁.showPrec n (Just x) = showParen (9 Nat.< n) (showString "just " ∘ showPrec 10 x)

--   ShowList : ⦃ Show a ⦄ → Show (List a)
--   ShowList = record {Show₁ (λ where .Show₁.showPrec _ → showList)}

-- {-# COMPILE AGDA2HS ShowBool #-}
-- {-# COMPILE AGDA2HS ShowMaybe #-}
-- -- NB: assuming we always get copatterns (from outer-most records):
-- --    1. normal case (no minimality, just as before)
-- --    2. minimal primitive used (chase down definition and inline it)
-- --    3. minimal derived method used (ignore)

-- {- OUTPUT
-- instance Show Bool where
--   show True = "true"
--   show False = "false"

--   showList [] = ....
--   showList (true : ...
--   showList (false : ...

-- instance Show a => Show (Maybe a) where
--   showPrec n Nothing  = ...
--   showPrec n (Just x) = ...

-- instance Show a => Show (List a) where
--   showPrec _ = showList
-- -}
