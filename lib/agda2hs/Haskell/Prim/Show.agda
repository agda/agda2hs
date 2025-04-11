
module Haskell.Prim.Show where

open import Haskell.Prim
open import Haskell.Prim.String
open import Haskell.Prim.List
open import Haskell.Prim.Word
open import Haskell.Prim.Double
open import Haskell.Prim.Maybe
open import Haskell.Prim.Eq
open import Haskell.Prim.Tuple
open import Haskell.Prim.Ord
open import Haskell.Prim.Either
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool
open import Haskell.Prim.Int
open import Haskell.Prim.Foldable


--------------------------------------------------
-- Show

ShowS : Type
ShowS = String → String

showChar : Char → ShowS
showChar = _∷_

showString : String → ShowS
showString = _++_

showParen : Bool → ShowS → ShowS
showParen False s = s
showParen True  s = showString "(" ∘ s ∘ showString ")"

defaultShowList : (a → ShowS) → List a → ShowS
defaultShowList shows = λ where
  []       → showString "[]"
  (x ∷ xs) → showString "["
           ∘ foldl (λ s x → s ∘ showString "," ∘ shows x) (shows x) xs
           ∘ showString "]"

-- ** base
record Show (a : Type) : Type where
  field
    showsPrec : Int → a → ShowS
    showList  : List a → ShowS
    show      : a → String
-- ** export
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
-- ** export
open Show ⦃...⦄ public

shows : ⦃ Show a ⦄ → a → ShowS
shows = showsPrec 0

{-# COMPILE AGDA2HS Show existing-class #-}

-- ** instances
instance
  iShow₂Nat : Show₂ Nat
  iShow₂Nat .Show₂.show = primStringToList ∘ primShowNat

  iShowNat : Show Nat
  iShowNat = record {Show₂ iShow₂Nat}

  iShow₂Integer : Show₂ Integer
  iShow₂Integer .Show₂.show = showInteger

  iShowInteger : Show Integer
  iShowInteger = record {Show₂ iShow₂Integer}

  iShow₂Int : Show₂ Int
  iShow₂Int .Show₂.show = showInt

  iShowInt : Show Int
  iShowInt = record{Show₂ iShow₂Int}

  iShow₂Word : Show₂ Word
  iShow₂Word .Show₂.show = showWord

  iShowWord : Show Word
  iShowWord = record{Show₂ iShow₂Word}

  iShow₂Double : Show₂ Double
  iShow₂Double .Show₂.show = primStringToList ∘ primShowFloat

  iShowDouble : Show Double
  iShowDouble = record{Show₂ iShow₂Double}

  iShow₂Bool : Show₂ Bool
  iShow₂Bool .Show₂.show = λ where False → "False"; True → "True"

  iShowBool : Show Bool
  iShowBool = record{Show₂ iShow₂Bool}

  iShow₁Char : Show₁ Char
  iShow₁Char .Show₁.showsPrec _ = showString ∘ primStringToList ∘ primShowChar

  iShowChar : Show Char
  iShowChar = record{Show₁ iShow₁Char}

  iShow₁List : ⦃ Show a ⦄ → Show₁ (List a)
  iShow₁List .Show₁.showsPrec _ = showList

  iShowList : ⦃ Show a ⦄ → Show (List a)
  iShowList = record{Show₁ iShow₁List}

private
  showApp₁ : ⦃ Show a ⦄ → Int → String → a → ShowS
  showApp₁ p tag x = showParen (p > 10) $
    showString tag ∘ showString " " ∘ showsPrec 11 x

instance
  iShow₁Maybe : ⦃ Show a ⦄ → Show₁ (Maybe a)
  iShow₁Maybe .Show₁.showsPrec = λ where
    p Nothing  → showString "Nothing"
    p (Just x) → showApp₁ p "Just" x

  iShowMaybe : ⦃ Show a ⦄ → Show (Maybe a)
  iShowMaybe = record{Show₁ iShow₁Maybe}

  iShow₁Either : ⦃ Show a ⦄ → ⦃ Show b ⦄ → Show₁ (Either a b)
  iShow₁Either .Show₁.showsPrec = λ where
    p (Left  x) → showApp₁ p "Left"  x
    p (Right y) → showApp₁ p "Right" y

  iShowEither : ⦃ Show a ⦄ → ⦃ Show b ⦄ → Show (Either a b)
  iShowEither = record{Show₁ iShow₁Either}

instance
  iShow₁Tuple₂ : ⦃ Show a ⦄ → ⦃ Show b ⦄ → Show₁ (a × b)
  iShow₁Tuple₂ .Show₁.showsPrec = λ _ → λ where
    (x , y) → showString "(" ∘ shows x ∘ showString ", " ∘ shows y ∘ showString ")"

  iShowTuple₂ : ⦃ Show a ⦄ → ⦃ Show b ⦄ → Show (a × b)
  iShowTuple₂ = record{Show₁ iShow₁Tuple₂}

  iShow₁Tuple₃ : ⦃ Show a ⦄ → ⦃ Show b ⦄ → ⦃ Show c ⦄ → Show₁ (a × b × c)
  iShow₁Tuple₃ .Show₁.showsPrec = λ _ → λ where
    (x , y , z) → showString "(" ∘ shows x ∘ showString ", " ∘ shows y ∘ showString ", " ∘ shows z ∘ showString ")"

  iShowTuple₃ : ⦃ Show a ⦄ → ⦃ Show b ⦄ → ⦃ Show c ⦄ → Show (a × b × c)
  iShowTuple₃ = record{Show₁ iShow₁Tuple₃}
