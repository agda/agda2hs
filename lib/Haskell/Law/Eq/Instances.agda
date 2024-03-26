module Haskell.Law.Eq.Instances where

open import Agda.Builtin.Char.Properties renaming (primCharToNatInjective to c2n-injective)
open import Agda.Builtin.Word.Properties renaming (primWord64ToNatInjective to w2n-injective)

open import Haskell.Prim
open import Haskell.Prim.Eq

open import Haskell.Prim.Either using ( Either; Left; Right )
open import Haskell.Prim.Int    using ( Int; int64 )
open import Haskell.Prim.Maybe
open import Haskell.Prim.Ord    using ( Ordering; LT; GT; EQ )
open import Haskell.Prim.Tuple
open import Haskell.Prim.Word   using ( Word )

open import Haskell.Extra.Dec   using ( mapReflects )

open import Haskell.Law.Eq.Def
open import Haskell.Law.Equality

open import Haskell.Law.Either
open import Haskell.Law.Int
open import Haskell.Law.Integer
open import Haskell.Law.List    using ( ∷-injective-left; ∷-injective-right )
open import Haskell.Law.Maybe
open import Haskell.Law.Nat

instance
  iLawfulEqNat : IsLawfulEq Nat
  iLawfulEqNat .isEquality zero    zero    = refl
  iLawfulEqNat .isEquality zero    (suc _) = λ ()
  iLawfulEqNat .isEquality (suc _) zero    = λ ()
  iLawfulEqNat .isEquality (suc x) (suc y) = mapReflects 
    (cong suc) 
    suc-injective 
    (isEquality x y)

  iLawfulEqWord : IsLawfulEq Word
  iLawfulEqWord .isEquality x y 
    with (w2n x) in h₁ | (w2n y) in h₂ 
  ... | a | b  = mapReflects
    (λ h → w2n-injective x y $ sym $ trans (trans h₂ $ sym h) (sym h₁))
    (λ h → trans (sym $ trans (cong w2n (sym h)) h₁) h₂)
    (isEquality a b)

  iLawfulEqBool : IsLawfulEq Bool
  iLawfulEqBool .isEquality False False = refl
  iLawfulEqBool .isEquality False True  = λ()
  iLawfulEqBool .isEquality True  False = λ()
  iLawfulEqBool .isEquality True  True  = refl

  iLawfulEqChar : IsLawfulEq Char
  iLawfulEqChar .isEquality x y 
    with (c2n x) in h₁ | (c2n y) in h₂ 
  ... | a | b  = mapReflects { a ≡ b } { x ≡ y } { eqNat a b } 
    (λ h → c2n-injective x y $ sym $ trans (trans h₂ $ sym h) (sym h₁))
    (λ h → trans (sym $ trans (cong c2n (sym h)) h₁) h₂)
    (isEquality a b)

  iLawfulEqEither : ⦃ iEqA : Eq a ⦄ → ⦃ iEqB : Eq b ⦄ 
    → ⦃ IsLawfulEq a ⦄ → ⦃ IsLawfulEq b ⦄ 
    → IsLawfulEq (Either a b)
  iLawfulEqEither .isEquality (Left  _) (Right _) = λ ()
  iLawfulEqEither .isEquality (Right _) (Left  _) = λ ()
  iLawfulEqEither .isEquality (Left  x) (Left  y) = mapReflects 
    (cong Left) (Left-injective) (isEquality x y)
  iLawfulEqEither .isEquality (Right x) (Right y) = mapReflects 
    (cong Right) (Right-injective) (isEquality x y)

  iLawfulEqInt : IsLawfulEq Int
  iLawfulEqInt .isEquality (int64 x) (int64 y) = mapReflects
    (cong int64) int64-injective (isEquality x y) 

  iLawfulEqInteger : IsLawfulEq Integer
  iLawfulEqInteger .isEquality (pos n)    (pos m)    = mapReflects 
    (cong pos) pos-injective (isEquality n m)
  iLawfulEqInteger .isEquality (pos _)    (negsuc _) = λ () 
  iLawfulEqInteger .isEquality (negsuc _) (pos _)    = λ ()
  iLawfulEqInteger .isEquality (negsuc n) (negsuc m) = mapReflects 
    (cong negsuc) neg-injective (isEquality n m)
  
  iLawfulEqList : ⦃ iEqA : Eq a ⦄ → ⦃ IsLawfulEq a ⦄ → IsLawfulEq (List a)
  iLawfulEqList .isEquality []       []      = refl
  iLawfulEqList .isEquality []       (_ ∷ _) = λ ()
  iLawfulEqList .isEquality (_ ∷ _)  []      = λ ()
  iLawfulEqList .isEquality (x ∷ xs) (y ∷ ys) 
    with (x == y) in h₁
  ... | True  = mapReflects 
    (λ h → cong₂ (_∷_) (equality h₁)  h) 
    ∷-injective-right 
    (isEquality xs ys)
  ... | False = λ h → (nequality h₁) (∷-injective-left h)

  iLawfulEqMaybe : ⦃ iEqA : Eq a ⦄ → ⦃ IsLawfulEq a ⦄ → IsLawfulEq (Maybe a)
  iLawfulEqMaybe .isEquality Nothing  Nothing  = refl
  iLawfulEqMaybe .isEquality Nothing  (Just _) = λ()
  iLawfulEqMaybe .isEquality (Just _) Nothing  = λ()
  iLawfulEqMaybe .isEquality (Just x) (Just y) = mapReflects 
    (cong Just) Just-injective (isEquality x y)

  iLawfulEqOrdering : IsLawfulEq Ordering
  iLawfulEqOrdering .isEquality LT LT = refl
  iLawfulEqOrdering .isEquality LT EQ = λ()
  iLawfulEqOrdering .isEquality LT GT = λ()
  iLawfulEqOrdering .isEquality EQ LT = λ()
  iLawfulEqOrdering .isEquality EQ EQ = refl
  iLawfulEqOrdering .isEquality EQ GT = λ()
  iLawfulEqOrdering .isEquality GT LT = λ()
  iLawfulEqOrdering .isEquality GT EQ = λ()
  iLawfulEqOrdering .isEquality GT GT = refl

  iLawfulEqTuple₂ : ⦃ iEqA : Eq a ⦄ ⦃ iEqB : Eq b ⦄
    → ⦃ IsLawfulEq a ⦄ → ⦃ IsLawfulEq b ⦄
    → IsLawfulEq (a × b)
  iLawfulEqTuple₂ .isEquality (x₁ , x₂) (y₁ , y₂)
    with (x₁ == y₁) in h₁
  ... | True  = mapReflects
    (λ h → cong₂ _,_ (equality h₁) h) 
    (cong snd) 
    (isEquality x₂ y₂)
  ... | False = λ h → exFalso (equality' (cong fst h)) h₁

  iLawfulEqTuple₃ : ⦃ iEqA : Eq a ⦄ ⦃ iEqB : Eq b ⦄ ⦃ iEqC : Eq c ⦄
    → ⦃ IsLawfulEq a ⦄ → ⦃ IsLawfulEq b ⦄ → ⦃ IsLawfulEq c ⦄
    → IsLawfulEq (a × b × c)
  iLawfulEqTuple₃ .isEquality (x₁ , x₂ , x₃) (y₁ , y₂ , y₃) 
    with (x₁ == y₁) in h₁ 
  ... | True  = mapReflects
    (λ h → cong₂ (λ a (b , c) → a , b , c) (equality h₁) h) 
    (cong λ h → snd₃ h , thd₃ h) 
    (isEquality (x₂ , x₃) (y₂ , y₃))
  ... | False = λ h → exFalso (equality' (cong  fst₃ h)) h₁ 

  iLawfulEqUnit : IsLawfulEq ⊤
  iLawfulEqUnit .isEquality tt tt = refl
