
module Haskell.Prim.Show where

open import Agda.Builtin.Char
open import Agda.Builtin.Nat
import Agda.Builtin.String as Str

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
showParen false s = s
showParen true  s = showString "(" ∘ s ∘ showString ")"

record Show (a : Set) : Set where
  field
    showsPrec : Int → a → ShowS
    showList  : List a → ShowS

  shows : a → ShowS
  shows = showsPrec 0

  show : a → String
  show x = shows x ""

defaultShowList : (a → ShowS) → List a → ShowS
defaultShowList _     []       = showString "[]"
defaultShowList shows (x ∷ xs) = showString "[" ∘ foldl (λ s x → s ∘ showString "," ∘ shows x) (shows x) xs ∘ showString "]"

open Show ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Show existing-class #-}

private
  makeShow : (a → String) → Show a
  makeShow sh .showsPrec _ = showString ∘ sh
  makeShow sh .showList    = defaultShowList (showString ∘ sh)

  makeShowsPrec : (Int → a → ShowS) → Show a
  makeShowsPrec shp .showsPrec = shp
  makeShowsPrec shp .showList = defaultShowList (shp 0)

instance
  iShowNat : Show Nat
  iShowNat = makeShow (Str.primStringToList ∘ Str.primShowNat)

  iShowInteger : Show Integer
  iShowInteger = makeShow showInteger

  iShowInt : Show Int
  iShowInt = makeShow showInt

  iShowWord : Show Word
  iShowWord = makeShow showWord

  iShowDouble : Show Double
  iShowDouble = makeShow (Str.primStringToList ∘ primShowFloat)

  iShowBool : Show Bool
  iShowBool = makeShow λ where false → "False"; true → "True"

  iShowChar : Show Char
  iShowChar .showsPrec _ = showString ∘ Str.primStringToList ∘ Str.primShowChar
  iShowChar .showList    = showString ∘ Str.primStringToList ∘ Str.primShowString ∘ Str.primStringFromList

  iShowList : ⦃ Show a ⦄ → Show (List a)
  iShowList .showsPrec _ = showList
  iShowList .showList    = defaultShowList showList

private
  showApp₁ : ⦃ Show a ⦄ → Int → String → a → ShowS
  showApp₁ p tag x = showParen (p > 10) $ showString tag ∘ showString " " ∘ showsPrec 11 x

instance
  iShowMaybe : ⦃ Show a ⦄ → Show (Maybe a)
  iShowMaybe = makeShowsPrec λ where p Nothing  → showString "Nothing"
                                     p (Just x) → showApp₁ p "Just" x

  iShowEither : ⦃ Show a ⦄ → ⦃ Show b ⦄ → Show (Either a b)
  iShowEither = makeShowsPrec λ where p (Left  x) → showApp₁ p "Left"  x
                                      p (Right y) → showApp₁ p "Right" y

private
  -- Minus the parens
  showTuple : ∀ {as} → ⦃ All Show as ⦄ → Tuple as → ShowS
  showTuple             []       = showString ""
  showTuple ⦃ allCons ⦄ (x ∷ []) = shows x
  showTuple ⦃ allCons ⦄ (x ∷ xs) = shows x ∘ showString "," ∘ showTuple xs

instance
  iShowTuple : ∀ {as} → ⦃ All Show as ⦄ → Show (Tuple as)
  iShowTuple = makeShowsPrec λ _ → showParen true ∘ showTuple
