module Haskell.Law.List where

open import Haskell.Law.Equality
open import Haskell.Prim renaming (addNat to _+ₙ_)
open import Haskell.Prim.Foldable
open import Haskell.Prim.List

[]≠∷ : ∀ x (xs : List a) → [] ≠ x ∷ xs
[]≠∷ x xs ()

--------------------------------------------------
-- _∷_

module _ {x y : a} {xs ys : List a} where  
  ∷-injective-left : x ∷ xs ≡ y ∷ ys → x ≡ y
  ∷-injective-left refl = refl

  ∷-injective-right : x ∷ xs ≡ y ∷ ys → xs ≡ ys
  ∷-injective-right refl = refl

--------------------------------------------------
-- map

map-id : (xs : List a) → map id xs ≡ xs
map-id []       = refl
map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

map-++ : ∀ (f : a → b) xs ys → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f [] ys       = refl
map-++ f (x ∷ xs) ys = cong (f x ∷_) (map-++ f xs ys)

lengthMap : ∀ (f : a → b) xs → lengthNat (map f xs) ≡ lengthNat xs
lengthMap f []       = refl
lengthMap f (x ∷ xs) = cong suc (lengthMap f xs)

map-∘ : ∀ (g : b → c) (f : a → b) xs → map (g ∘ f) xs ≡ (map g ∘ map f) xs
map-∘ g f []       = refl
map-∘ g f (x ∷ xs) = cong (_ ∷_) (map-∘ g f xs)

--------------------------------------------------
-- _++_

lengthNat-++ : ∀ (xs : List a) {ys} →
            lengthNat (xs ++ ys) ≡ lengthNat xs +ₙ lengthNat ys
lengthNat-++ []       = refl
lengthNat-++ (x ∷ xs) = cong suc (lengthNat-++ xs)

++-[] : ∀ (xs : List a) → xs ++ [] ≡ xs
++-[] [] = refl
++-[] (x ∷ xs) rewrite ++-[] xs = refl

[]-++ : ∀ (xs : List a) → [] ++ xs ≡ xs
[]-++ xs = refl

++-assoc : ∀ (xs ys zs : List a) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl

++-∷-assoc : ∀ xs y (ys : List a) → xs ++ y ∷ ys ≡ (xs ++ y ∷ []) ++ ys
++-∷-assoc [] y ys = refl
++-∷-assoc (x ∷ xs) y ys = cong (x ∷_) (++-∷-assoc xs y ys)

∷-++-assoc : ∀ x xs (ys : List a) → (x ∷ xs) ++ ys ≡ x ∷ (xs ++ ys)
∷-++-assoc x xs ys = refl

++-identity-right-unique : ∀ (xs : List a) {ys} → xs ≡ xs ++ ys → ys ≡ []
++-identity-right-unique []       refl = refl
++-identity-right-unique (x ∷ xs) eq   =
  ++-identity-right-unique xs (∷-injective-right eq)

++-identity-left-unique : ∀ {xs} (ys : List a) → xs ≡ ys ++ xs → ys ≡ []
++-identity-left-unique               []       _  = refl
++-identity-left-unique {xs = x ∷ xs} (y ∷ ys) eq
  with ++-identity-left-unique (ys ++ (x ∷ [])) (begin
        xs                  ≡⟨ ∷-injective-right eq ⟩
        ys ++ x ∷ xs        ≡⟨ sym (++-assoc ys (x ∷ []) xs) ⟩
        (ys ++ x ∷ []) ++ xs ∎)
++-identity-left-unique {xs = x ∷ xs} (y ∷ []   ) eq | ()
++-identity-left-unique {xs = x ∷ xs} (y ∷ _ ∷ _) eq | ()

++-cancel-left : ∀ (xs ys : List a) {zs} → xs ++ ys ≡ xs ++ zs → ys ≡ zs
++-cancel-left []       ys eq = eq
++-cancel-left (x ∷ xs) ys eq = ++-cancel-left xs ys (∷-injective-right eq)

++-cancel-right : ∀ (xs ys : List a) {zs} → xs ++ zs ≡ ys ++ zs → xs ≡ ys
++-cancel-right []       []       eq = refl
++-cancel-right (x ∷ xs) []       eq = ++-identity-left-unique (x ∷ xs) (sym eq)
++-cancel-right []       (y ∷ ys) eq = sym $ ++-identity-left-unique (y ∷ ys) eq
++-cancel-right (x ∷ xs) (y ∷ ys) eq 
  rewrite ∷-injective-left eq = cong (y ∷_) $ ++-cancel-right xs ys (∷-injective-right eq)

++-conical-left : (xs ys : List a) → xs ++ ys ≡ [] → xs ≡ []
++-conical-left [] _ refl = refl

++-conical-right : (xs ys : List a) → xs ++ ys ≡ [] → ys ≡ []
++-conical-right [] _ refl = refl

∷-not-identity : ∀ x (xs ys : List a) → (x ∷ xs) ++ ys ≡ ys → ⊥
∷-not-identity x xs ys eq = []≠∷ x xs (sym $ ++-identity-left-unique (x ∷ xs) (sym eq))

--------------------------------------------------
-- foldr

foldr-universal : ∀ (h : List a → b) f e → (h [] ≡ e) →
                  (∀ x xs → h (x ∷ xs) ≡ f x (h xs)) →
                  ∀ xs → h xs ≡ foldr f e xs
foldr-universal h f e base step []       = base
foldr-universal h f e base step (x ∷ xs) rewrite step x xs = cong (f x) (foldr-universal h f e base step xs) 

foldr-cong : ∀ {f g : a → b → b} {d e : b} →
            (∀ x y → f x y ≡ g x y) → d ≡ e →
             ∀ (xs : List a) → foldr f d xs ≡ foldr g e xs
foldr-cong f≡g d≡e []       = d≡e
foldr-cong f≡g d≡e (x ∷ xs) rewrite foldr-cong f≡g d≡e xs = f≡g x _

foldr-fusion : (h : b → c) {f : a → b → b} {g : a → c → c} (e : b) →
               (∀ x y → h (f x y) ≡ g x (h y)) →
               ∀ (xs : List a) → h (foldr f e xs) ≡ foldr g (h e) xs
foldr-fusion h {f} {g} e fuse =
  foldr-universal (h ∘ foldr f e) g (h e) refl
                  (λ x xs → fuse x (foldr f e xs))