
open import Haskell.Prelude
open import Haskell.Extra.Refinement
open import Haskell.Law.Equality

private variable
    @0 n : Nat

data Vec (a : Set) : @0 Nat → Set where
    [] : Vec a 0
    _∷_ : a → Vec a n → Vec a (suc n)

{-# COMPILE AGDA2HS Vec to List #-}

test1 : Vec Int 3
test1 = 1 ∷ 2 ∷ 3 ∷ []

{-# COMPILE AGDA2HS test1 #-}

listToVec : (xs : List a) → Vec a (lengthNat xs)
listToVec [] = []
listToVec (x ∷ xs) = x ∷ listToVec xs

{-# COMPILE AGDA2HS listToVec transparent #-}

vecToList : Vec a n → List a
vecToList [] = []
vecToList (x ∷ xs) = x ∷ vecToList xs

{-# COMPILE AGDA2HS vecToList transparent #-}

test2 : Vec Int 3
test2 = listToVec (map (_+ 1) (vecToList (1 ∷ 2 ∷ 3 ∷ [])))

{-# COMPILE AGDA2HS test2 #-}

-- Not using `length` since compile-to is not yet compatible with type classes
llength : List a → Nat
llength [] = 0
llength (x ∷ xs) = 1 + llength xs

{-# COMPILE AGDA2HS llength #-}

vlength : Vec a n → ∃ Nat (_≡ n)
vlength [] = 0 ⟨ refl ⟩
vlength (x ∷ xs) =
  let n ⟨ eq ⟩ = vlength xs
  in  (1 + n) ⟨ cong suc eq ⟩

{-# COMPILE AGDA2HS vlength to llength #-}

test3 : ∃ Nat (_≡ 3)
test3 = vlength test1

{-# COMPILE AGDA2HS test3 #-}

lfoldl : (b → a → b) → b → List a → b
lfoldl f v [] = v
lfoldl f v (x ∷ xs) = lfoldl f (f v x) xs

{-# COMPILE AGDA2HS lfoldl #-}

vfoldl : (b : @0 Nat → Set) → (∀ {@0 n} → b n → a → b (suc n)) → b 0 → Vec a n → b n
vfoldl b f v [] = v
vfoldl b f v (x ∷ xs) = vfoldl (λ n → b (suc n)) f (f v x) xs

{-# COMPILE AGDA2HS vfoldl to lfoldl #-}

vreverse : Vec a n → Vec a n
vreverse {a = a} = vfoldl (Vec a) (λ xs x → x ∷ xs) []

{-# COMPILE AGDA2HS vreverse #-}
