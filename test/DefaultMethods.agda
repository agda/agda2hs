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

{-# FOREIGN AGDA2HS
{-# LANGUAGE TypeSynonymInstances #-}
import Prelude hiding (Show, ShowS, show, showList, showString, showParen, Ord, (<), (>))
#-}

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

OB : Ord₁ Bool
OB .Ord₁._<_ false b = b
OB .Ord₁._<_ true  _ = false

instance
  OrdBool₀ : Ord Bool
  OrdBool₀ ._<_ = Ord₁._<_ OB
  OrdBool₀ ._>_ = Ord₁._>_ OB
{-# COMPILE AGDA2HS OrdBool₀ #-}

data Bool1 : Set where
  Mk1 : Bool -> Bool1
{-# COMPILE AGDA2HS Bool1 #-}
instance
  OrdBool₁ : Ord Bool1
  OrdBool₁ = record {Ord₁ ord₁}
    where
      ord₁ : Ord₁ Bool1
      ord₁ .Ord₁._<_ (Mk1 false) (Mk1 b) = b
      ord₁ .Ord₁._<_ (Mk1 true)  _       = false
{-# COMPILE AGDA2HS OrdBool₁ #-}

data Bool2 : Set where
  Mk2 : Bool -> Bool2
{-# COMPILE AGDA2HS Bool2 #-}
instance
  OrdBool₂ : Ord Bool2
  OrdBool₂ = record {_<_ = _<:_; _>_ = flip _<:_}
    where
      _<:_ : Bool2 → Bool2 → Bool
      (Mk2 false) <: (Mk2 b) = b
      (Mk2 true)  <: _       = false
{-# COMPILE AGDA2HS OrdBool₂ #-}

data Bool3 : Set where
  Mk3 : Bool -> Bool3
{-# COMPILE AGDA2HS Bool3 #-}
instance
  OrdBool₃ : Ord Bool3
  OrdBool₃ = record {Ord₁ (λ where .Ord₁._<_ → _<:_)}
    where
      _<:_ : Bool3 → Bool3 → Bool
      (Mk3 false) <: (Mk3 b) = b
      (Mk3 true)  <: _       = false
{-# COMPILE AGDA2HS OrdBool₃ #-}

data Bool4 : Set where
  Mk4 : Bool -> Bool4
{-# COMPILE AGDA2HS Bool4 #-}
lift4 : (Bool → Bool → a) → (Bool4 → Bool4 → a)
lift4 f (Mk4 x) (Mk4 y) = f x y
{-# COMPILE AGDA2HS lift4 #-}
instance
  OrdBool₄ : Ord Bool4
  OrdBool₄ = record {Ord₁ (λ where .Ord₁._<_ → lift4 (λ x y → not x && y))}
{-# COMPILE AGDA2HS OrdBool₄ #-}

data Bool5 : Set where
  Mk5 : Bool -> Bool5
{-# COMPILE AGDA2HS Bool5 #-}
instance
  OrdBool₅ : Ord Bool5
  OrdBool₅ = record {Ord₂ (λ where .Ord₂._>_ → _>:_)}
    where
      _>:_ : Bool5 → Bool5 → Bool
      (Mk5 false) >: _       = false
      (Mk5 true)  >: (Mk5 b) = not b
{-# COMPILE AGDA2HS OrdBool₅ #-}

data Bool6 : Set where
  Mk6 : Bool -> Bool6
{-# COMPILE AGDA2HS Bool6 #-}
instance
  OrdBool₆ : Ord Bool6
  OrdBool₆ = record {Ord₂ (λ where .Ord₂._>_ → _>:_); _<_ = flip _>:_}
    where
      _>:_ : Bool6 → Bool6 → Bool
      (Mk6 false) >: _       = false
      (Mk6 true)  >: (Mk6 b) = not b
{-# COMPILE AGDA2HS OrdBool₆ #-}

instance
  Ordℕ : Ord Nat
  Ordℕ = record {Ord₁ (λ where .Ord₁._<_ → Nat._<_)}
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

SB : Show₂ Bool
SB .Show₂.show true  = "true"
SB .Show₂.show false = "false"

instance
  ShowBool : Show Bool
  ShowBool .show     = Show₂.show SB
  ShowBool .showPrec = Show₂.showPrec SB
  ShowBool .showList []       = showString ""
  ShowBool .showList (true ∷ bs) = showString "1" ∘ showList bs
  ShowBool .showList (false ∷ bs) = showString "0" ∘ showList bs
{-# COMPILE AGDA2HS ShowBool #-}

instance
  ShowMaybe : ⦃ Show a ⦄ → Show (Maybe a)
  ShowMaybe {a = a} = record {Show₁ s₁}
    where
      s₁ : Show₁ (Maybe a)
      s₁ .Show₁.showPrec n Nothing = showString "nothing"
      s₁ .Show₁.showPrec n (Just x) = showParen true {-(9 < n)-} (showString "just " ∘ showPrec 10 x)
{-# COMPILE AGDA2HS ShowMaybe #-}

instance
  ShowList : ⦃ Show a ⦄ → Show (List a)
  ShowList = record {Show₁ (λ where .Show₁.showPrec _ → showList)}
{-# COMPILE AGDA2HS ShowList #-}
