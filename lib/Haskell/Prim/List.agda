
module Haskell.Prim.List where

open import Haskell.Prim
open import Haskell.Prim.Bool
open import Haskell.Prim.Tuple
open import Haskell.Prim.Int


--------------------------------------------------
-- List

map : (a → b) → List a → List b
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

infixr 5 _++_
_++_ : ∀ {@0 ℓ} {@0 a : Set ℓ} → List a → List a → List a
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

filter : (a → Bool) → List a → List a
filter p []       = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs

scanl : (b → a → b) → b → List a → List b
scanl f z []       = z ∷ []
scanl f z (x ∷ xs) = z ∷ scanl f (f z x) xs

scanr : (a → b → b) → b → List a → List b
scanr f z [] = z ∷ []
scanr f z (x ∷ xs) =
  case scanr f z xs of λ where
    []         → [] -- impossible
    qs@(q ∷ _) → f x q ∷ qs

scanl1 : (a → a → a) → List a → List a
scanl1 f []       = []
scanl1 f (x ∷ xs) = scanl f x xs

scanr1 : (a → a → a) → List a → List a
scanr1 f []       = []
scanr1 f (x ∷ []) = x ∷ []
scanr1 f (x ∷ xs) =
  case scanr1 f xs of λ where
    []         → [] -- impossible
    qs@(q ∷ _) → f x q ∷ qs

takeWhile : (a → Bool) → List a → List a
takeWhile p [] = []
takeWhile p (x ∷ xs) = if p x then x ∷ takeWhile p xs else []

dropWhile : (a → Bool) → List a → List a
dropWhile p [] = []
dropWhile p (x ∷ xs) = if p x then dropWhile p xs else x ∷ xs

span : (a → Bool) → List a → List a × List a
span p [] = [] , []
span p (x ∷ xs) = if p x then first (x ∷_) (span p xs)
                         else ([] , x ∷ xs)

break : (a → Bool) → List a → List a × List a
break p = span (not ∘ p)

zipWith : (a → b → c) → List a → List b → List c
zipWith f []       _        = []
zipWith f _        []       = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

zip : List a → List b → List (a × b)
zip = zipWith _,_

zipWith3 : (a → b → c → d) → List a → List b → List c → List d
zipWith3 f []       _        _        = []
zipWith3 f _        []       _        = []
zipWith3 f _        _        []       = []
zipWith3 f (x ∷ xs) (y ∷ ys) (z ∷ zs) = f x y z ∷ zipWith3 f xs ys zs

zip3 : List a → List b → List c → List (a × b × c)
zip3 = zipWith3 _,_,_

unzip : List (a × b) → List a × List b
unzip []              = [] , []
unzip ((x , y) ∷ xys) = (x ∷_) *** (y ∷_) $ unzip xys

unzip3 : List (a × b × c) → List a × List b × List c
unzip3 []                   = [] , [] , []
unzip3 ((x , y , z) ∷ xyzs) =
  case unzip3 xyzs of λ where
    (xs , ys , zs) → x ∷ xs , y ∷ ys , z ∷ zs

takeNat : Nat → List a → List a
takeNat n       [] = []
takeNat zero    xs = []
takeNat (suc n) (x ∷ xs) = x ∷ takeNat n xs

take : (n : Int) → @0 ⦃ IsNonNegativeInt n ⦄ → List a → List a
take n xs = takeNat (intToNat n) xs

dropNat : Nat → List a → List a
dropNat n       [] = []
dropNat zero    xs = xs
dropNat (suc n) (_ ∷ xs) = dropNat n xs

drop : (n : Int) → @0 ⦃ IsNonNegativeInt n ⦄ → List a → List a
drop n xs = dropNat (intToNat n) xs

splitAtNat : (n : Nat) → List a → List a × List a
splitAtNat _       []       = [] , []
splitAtNat 0       xs       = [] , xs
splitAtNat (suc n) (x ∷ xs) = first (x ∷_) (splitAtNat n xs)

splitAt : (n : Int) → @0 ⦃ IsNonNegativeInt n ⦄ → List a → List a × List a
splitAt n xs = splitAtNat (intToNat n) xs

head : (xs : List a) → @0 ⦃ NonEmpty xs ⦄ → a
head (x ∷ _) = x

tail : (xs : List a) → @0 ⦃ NonEmpty xs ⦄ → List a
tail (_ ∷ xs) = xs

last : (xs : List a) → @0 ⦃ NonEmpty xs ⦄ → a
last (x ∷ [])         = x
last (_ ∷ xs@(_ ∷ _)) = last xs

init : (xs : List a) → @0 ⦃ NonEmpty xs ⦄ → List a
init (x ∷ [])         = []
init (x ∷ xs@(_ ∷ _)) = x ∷ init xs
