
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

ShowS : Set
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
record Show (a : Set) : Set where
  field
    showsPrec : Int → a → ShowS
    showList  : List a → ShowS
    show      : a → String
-- ** export
record Show₁ (a : Set) : Set where
  field showsPrec : Int → a → ShowS

  show : a → String
  show x = showsPrec 0 x ""

  showList : List a → ShowS
  showList = defaultShowList (showsPrec 0)
record Show₂ (a : Set) : Set where
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
private
  infix 0 showsPrec=_ show=_

  showsPrec=_ : (Int → a → ShowS) → Show a
  showsPrec=_ x = record {Show₁ (record {showsPrec = x})}

  show=_ : (a → String) → Show a
  show= x = record {Show₂ (record {show = x})}
instance
  iShowNat : Show Nat
  iShowNat = show= (primStringToList ∘ primShowNat)

  iShowInteger : Show Integer
  iShowInteger = show= showInteger

  iShowInt : Show Int
  iShowInt = show= showInt

  iShowWord : Show Word
  iShowWord = show= showWord

  iShowDouble : Show Double
  iShowDouble = show= (primStringToList ∘ primShowFloat)

  iShowBool : Show Bool
  iShowBool = show= λ where False → "False"; True → "True"

  iShowChar : Show Char
  iShowChar = showsPrec= λ _ → showString ∘ primStringToList ∘ primShowChar

  iShowList : ⦃ Show a ⦄ → Show (List a)
  iShowList = showsPrec= λ _ → showList
private
  showApp₁ : ⦃ Show a ⦄ → Int → String → a → ShowS
  showApp₁ p tag x = showParen (p > 10) $
    showString tag ∘ showString " " ∘ showsPrec 11 x
instance
  iShowMaybe : ⦃ Show a ⦄ → Show (Maybe a)
  iShowMaybe = showsPrec= λ where
    p Nothing  → showString "Nothing"
    p (Just x) → showApp₁ p "Just" x

  iShowEither : ⦃ Show a ⦄ → ⦃ Show b ⦄ → Show (Either a b)
  iShowEither = showsPrec= λ where
    p (Left  x) → showApp₁ p "Left"  x
    p (Right y) → showApp₁ p "Right" y
private
  -- Minus the parens
  showTuple : ⦃ All Show as ⦄ → Tuple as → ShowS
  showTuple ⦃ allNil  ⦄                 _        = showString ""
  showTuple ⦃ allCons ⦃ is = allNil ⦄ ⦄ (x ; tt) = shows x
  showTuple ⦃ allCons ⦄                 (x ; xs) = shows x
                                                 ∘ showString ", " ∘ showTuple xs
instance
  iShowTuple : ⦃ All Show as ⦄ → Show (Tuple as)
  iShowTuple = showsPrec= λ _ → showParen True ∘ showTuple
