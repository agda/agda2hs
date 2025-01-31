{-# OPTIONS --no-auto-inline #-}
module DefaultMethods where

open import Haskell.Prim using (ltNat)
open import Haskell.Prelude hiding
  ( Show; Show₁; Show₂; show; showsPrec; showList; defaultShowList
  ; Ord; _<_; _>_
  )

{-# FOREIGN AGDA2HS
{-# LANGUAGE TypeSynonymInstances #-}
import Prelude hiding (Show, show, showsPrec, showList, Ord, (<), (>))
#-}

-- ** Ord

record Ord (a : Type) : Type where
  field
    _<_ _>_ : a → a → Bool

record Ord₁ (a : Type) : Type where
  field
    _<_ : a → a → Bool

  _>_ : a → a → Bool
  x > y = y < x

record Ord₂ (a : Type) : Type where
  field
    _>_ : a → a → Bool

  _<_ : a → a → Bool
  _<_ = flip _>_

open Ord ⦃ ... ⦄

{-# COMPILE AGDA2HS Ord class Ord₁ Ord₂ #-}

OB : Ord₁ Bool
OB .Ord₁._<_ False b = b
OB .Ord₁._<_ True  _ = False

instance
  OrdBool₀ : Ord Bool
  OrdBool₀ ._<_ = Ord₁._<_ OB
  OrdBool₀ ._>_ = Ord₁._>_ OB
{-# COMPILE AGDA2HS OrdBool₀ #-}

data Bool1 : Type where
  Mk1 : Bool -> Bool1
{-# COMPILE AGDA2HS Bool1 #-}
instance
  OrdBool₁ : Ord Bool1
  OrdBool₁ = record {Ord₁ ord₁}
    where
      ord₁ : Ord₁ Bool1
      ord₁ .Ord₁._<_ (Mk1 False) (Mk1 b) = b
      ord₁ .Ord₁._<_ (Mk1 True)  _       = False
{-# COMPILE AGDA2HS OrdBool₁ #-}

data Bool2 : Type where
  Mk2 : Bool -> Bool2
{-# COMPILE AGDA2HS Bool2 #-}
instance
  OrdBool₂ : Ord Bool2
  OrdBool₂ = record {_<_ = _<:_; _>_ = flip _<:_}
    where
      _<:_ : Bool2 → Bool2 → Bool
      (Mk2 False) <: (Mk2 b) = b
      (Mk2 True)  <: _       = False
{-# COMPILE AGDA2HS OrdBool₂ #-}

data Bool3 : Type where
  Mk3 : Bool -> Bool3
{-# COMPILE AGDA2HS Bool3 #-}
instance
  OrdBool₃ : Ord Bool3
  OrdBool₃ = record {Ord₁ (λ where .Ord₁._<_ → _<:_)}
    where
      _<:_ : Bool3 → Bool3 → Bool
      (Mk3 False) <: (Mk3 b) = b
      (Mk3 True)  <: _       = False
{-# COMPILE AGDA2HS OrdBool₃ #-}

data Bool4 : Type where
  Mk4 : Bool -> Bool4
{-# COMPILE AGDA2HS Bool4 #-}
lift4 : (Bool → Bool → a) → (Bool4 → Bool4 → a)
lift4 f (Mk4 x) (Mk4 y) = f x y
{-# COMPILE AGDA2HS lift4 #-}
instance
  OrdBool₄ : Ord Bool4
  OrdBool₄ = record {Ord₁ (λ where .Ord₁._<_ → lift4 (λ x y → not x && y))}
{-# COMPILE AGDA2HS OrdBool₄ #-}

data Bool5 : Type where
  Mk5 : Bool -> Bool5
{-# COMPILE AGDA2HS Bool5 #-}
instance
  OrdBool₅ : Ord Bool5
  OrdBool₅ = record {Ord₂ (λ where .Ord₂._>_ → _>:_)}
    where
      _>:_ : Bool5 → Bool5 → Bool
      (Mk5 False) >: _       = False
      (Mk5 True)  >: (Mk5 b) = not b
{-# COMPILE AGDA2HS OrdBool₅ #-}

data Bool6 : Type where
  Mk6 : Bool -> Bool6
{-# COMPILE AGDA2HS Bool6 #-}
instance
  OrdBool₆ : Ord Bool6
  OrdBool₆ = record {Ord₂ (λ where .Ord₂._>_ → _>:_); _<_ = flip _>:_}
    where
      _>:_ : Bool6 → Bool6 → Bool
      (Mk6 False) >: _       = False
      (Mk6 True)  >: (Mk6 b) = not b
{-# COMPILE AGDA2HS OrdBool₆ #-}

instance
  Ordℕ : Ord Nat
  Ordℕ = record {Ord₁ (λ where .Ord₁._<_ → ltNat)}
-- {-# COMPILE AGDA2HS Ordℕ #-}

defaultShowList : (a → ShowS) → List a → ShowS
defaultShowList _     []
  = showString "[]"
defaultShowList shows (x ∷ xs)
  = showString "["
  ∘ foldl (λ s x → s ∘ showString "," ∘ shows x) (shows x) xs
  ∘ showString "]"
{-# COMPILE AGDA2HS defaultShowList #-}

record Show (a : Type) : Type where
  field
    show : a → String
    showsPrec : Int → a → ShowS
    showList : List a → ShowS

record Show₁ (a : Type) : Type where
  field showsPrec : Int → a → ShowS

  show : a → String
  show x = showsPrec 0 x ""

  showList : List a → ShowS
  showList = defaultShowList (showsPrec 0)

record Show₂ (a : Type) : Type where
  field show : a → String

  showsPrec : Int → a → ShowS
  showsPrec _ x s = show x ++ s

  showList : List a → ShowS
  showList = defaultShowList (showsPrec 0)

open Show ⦃ ... ⦄

{-# COMPILE AGDA2HS Show class Show₁ Show₂ #-}

SB : Show₂ Bool
SB .Show₂.show True  = "True"
SB .Show₂.show False = "False"

instance
  ShowBool : Show Bool
  ShowBool .show      = Show₂.show SB
  ShowBool .showsPrec = Show₂.showsPrec SB
  ShowBool .showList []           = showString ""
  ShowBool .showList (True ∷ bs)  = showString "1" ∘ showList bs
  ShowBool .showList (False ∷ bs) = showString "0" ∘ showList bs
{-# COMPILE AGDA2HS ShowBool #-}

instance
  ShowMaybe : ⦃ Show a ⦄ → Show (Maybe a)
  ShowMaybe {a = a} = record {Show₁ s₁}
    where
      s₁ : Show₁ (Maybe a)
      s₁ .Show₁.showsPrec n Nothing = showString "nothing"
      s₁ .Show₁.showsPrec n (Just x) = showParen True {-(9 < n)-} (showString "just " ∘ showsPrec 10 x)
{-# COMPILE AGDA2HS ShowMaybe #-}

instance
  ShowList : ⦃ Show a ⦄ → Show (List a)
  ShowList = record {Show₁ (λ where .Show₁.showsPrec _ → showList)}
{-# COMPILE AGDA2HS ShowList #-}
