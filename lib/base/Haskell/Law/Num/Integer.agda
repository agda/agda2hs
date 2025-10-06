module Haskell.Law.Num.Integer where

open import Haskell.Prim
open import Haskell.Prim.Num
open import Haskell.Prim.Integer

open import Haskell.Law.Equality
open import Haskell.Law.Num.Def
open import Haskell.Law.Num.Nat

-- Open the internal definitions because
-- these must be transparent for proofs.
open Haskell.Prim.Integer.Internal

addInteger-idˡ : ∀ (x : Integer) → 0 + x ≡ x
addInteger-idˡ (pos _)    = refl
addInteger-idˡ (negsuc _) = cong negsuc refl

addInteger-idʳ : ∀ (x : Integer) → x + 0 ≡ x
addInteger-idʳ (pos n)    = cong pos    $ addNat-idʳ n
addInteger-idʳ (negsuc _) = cong negsuc refl

mulInteger-idˡ : ∀ (x : Integer) → 1 * x ≡ x
mulInteger-idˡ (pos x)    = cong pos    (addNat-idʳ x)
mulInteger-idˡ (negsuc x) = cong negsuc (addNat-idʳ x)

mulInteger-idʳ : ∀ (x : Integer) → x * 1 ≡ x
mulInteger-idʳ (pos x)    = cong pos    (mulNat-idʳ x)
mulInteger-idʳ (negsuc x) = cong negsuc (mulNat-idʳ x)

subNat-refl : ∀ (x : Nat) → subNat x x ≡ 0
subNat-refl zero    = refl
subNat-refl (suc x) = subNat-refl x

n-n≡0-Nat : ∀ (x y : Nat) → subNat (x + y) x ≡ pos y
n-n≡0-Nat x       zero    rewrite addNat-idʳ x = subNat-refl x
n-n≡0-Nat zero    (suc _) = refl
n-n≡0-Nat (suc x) (suc y) = n-n≡0-Nat x (suc y)

n-n≡0-Integer : ∀ (x : Integer) → x + (negateInteger x) ≡ 0
n-n≡0-Integer (pos zero)    = refl
n-n≡0-Integer (pos (suc x)) = subNat-refl x
n-n≡0-Integer (negsuc x)    = subNat-refl x

mulInteger-zeroˡ : ∀ (x : Integer) → 0 * x ≡ 0
mulInteger-zeroˡ (pos _)    = refl
mulInteger-zeroˡ (negsuc _) = refl

mulInteger-zeroʳ : ∀ (x : Integer) → x * 0 ≡ 0
mulInteger-zeroʳ (pos n)    = cong pos (mulNat-zeroʳ n)
mulInteger-zeroʳ (negsuc n) rewrite mulNat-zeroʳ n = refl

addInteger-comm : ∀ (x y : Integer) → x + y ≡ y + x
addInteger-comm (pos x)    (pos y)    = cong pos (addNat-comm x y)
addInteger-comm (pos _)    (negsuc _) = refl
addInteger-comm (negsuc _) (pos _)    = refl
addInteger-comm (negsuc x) (negsuc y) = cong negsuc (cong suc (addNat-comm x y))

subNat|x-[y+z]≡x-y-z : ∀ (x y z : Nat) → subNat x (y + suc z) ≡ subNat x y + negsuc z
subNat|x-[y+z]≡x-y-z _       zero    _ = refl
subNat|x-[y+z]≡x-y-z zero    (suc y) z = cong negsuc (addNat-suc y z)
subNat|x-[y+z]≡x-y-z (suc x) (suc y) z = subNat|x-[y+z]≡x-y-z x y z

subNat|x-y+z≡[x+z]-y : ∀ (x y z : Nat) → subNat x y + pos (suc z) ≡ subNat (x + suc z) y
subNat|x-y+z≡[x+z]-y _       zero    _ = refl
subNat|x-y+z≡[x+z]-y zero    (suc _) _ = refl
subNat|x-y+z≡[x+z]-y (suc x) (suc y) z = subNat|x-y+z≡[x+z]-y x y z

subNat-cong-suc : ∀ (x y : Nat) → subNat (suc x) y ≡ pos 1 + subNat x y
subNat-cong-suc _       zero    = refl
subNat-cong-suc zero    (suc _) = refl
subNat-cong-suc (suc x) (suc y) = subNat-cong-suc x y

subNat|x+[y-z]≡[1+x]+[y-[1+z]] : ∀ (x y z : Nat) → pos x + subNat y z ≡ pos (suc x) + subNat y (suc z)
subNat|x+[y-z]≡[1+x]+[y-[1+z]] x zero    zero    = cong pos (addNat-idʳ x)
subNat|x+[y-z]≡[1+x]+[y-[1+z]] x (suc y) zero    = cong pos (addNat-suc x y)
subNat|x+[y-z]≡[1+x]+[y-[1+z]] _ zero    (suc _) = refl
subNat|x+[y-z]≡[1+x]+[y-[1+z]] x (suc y) (suc z) = subNat|x+[y-z]≡[1+x]+[y-[1+z]] x y z

subNat|x-y+[1+z]≡[1+x]+[z-y] : ∀ (x y z : Nat) → subNat x y + pos (suc z) ≡ pos (suc x) + subNat z y
subNat|x-y+[1+z]≡[1+x]+[z-y] x       zero    z    = cong pos (addNat-suc x z)
subNat|x-y+[1+z]≡[1+x]+[z-y] zero    (suc _) zero = refl
subNat|x-y+[1+z]≡[1+x]+[z-y] zero    (suc y) (suc z) = subNat-cong-suc z y
subNat|x-y+[1+z]≡[1+x]+[z-y] (suc x) (suc y) z       =
  subNat x y + pos (suc z)             ≡⟨ subNat|x-y+[1+z]≡[1+x]+[z-y] x y z ⟩
  pos (suc x)       + subNat z y       ≡⟨ subNat|x+[y-z]≡[1+x]+[y-[1+z]] (suc x) z y ⟩
  pos (suc (suc x)) + subNat z (suc y) ∎

subNat|[1+x+y]-z≡[1+x]+[y-z] : ∀ (x y z : Nat) → subNat (suc x + y) z ≡ pos (suc x) + subNat y z
subNat|[1+x+y]-z≡[1+x]+[y-z] _ _       zero    = refl
subNat|[1+x+y]-z≡[1+x]+[y-z] x zero    (suc z) = cong (λ eq → subNat eq z) (addNat-idʳ x)
subNat|[1+x+y]-z≡[1+x]+[y-z] x (suc y) (suc z) =
  subNat (x + suc y) z     ≡⟨ sym (subNat|x-y+z≡[x+z]-y x z y) ⟩
  subNat x z + pos (suc y) ≡⟨ subNat|x-y+[1+z]≡[1+x]+[z-y] x z y ⟩
  pos (suc x) + subNat y z ∎

subNat|x-y+[-[1+z]]≡x-z+[-[1+y]] : ∀ (x y z : Nat) → subNat x y + negsuc z ≡ subNat x z + negsuc y
subNat|x-y+[-[1+z]]≡x-z+[-[1+y]] x y z = begin
  subNat x y + negsuc z ≡⟨ sym (subNat|x-[y+z]≡x-y-z x y z) ⟩
  subNat x (y + suc z)  ≡⟨ cong (subNat x) (addNat-comm y (suc z)) ⟩
  subNat x (suc z + y)  ≡⟨ cong (subNat x) (sym (addNat-suc z y)) ⟩
  subNat x (z + suc y)  ≡⟨ subNat|x-[y+z]≡x-y-z x z y ⟩
  subNat x z + negsuc y ∎

subNat-cong-+ : ∀ (x y z : Nat) → subNat (x + y) (x + z) ≡ subNat y z
subNat-cong-+ x       y zero rewrite addNat-idʳ x = n-n≡0-Nat x y
subNat-cong-+ zero    _ (suc _) = refl
subNat-cong-+ (suc x) y (suc z) = subNat-cong-+ x y (suc z)

subNat-distrib-minus : ∀ (m n o : Nat) → subNat n o * pos m ≡ subNat (n * m) (o * m)
subNat-distrib-minus _       _       zero    = refl
subNat-distrib-minus zero    zero    (suc o) rewrite mulNat-zeroʳ o = refl
subNat-distrib-minus (suc _) zero    (suc _) = refl
subNat-distrib-minus zero    (suc n) (suc o) rewrite mulNat-zeroʳ o | mulInteger-zeroʳ (subNat n o) | mulNat-zeroʳ n = refl
subNat-distrib-minus (suc m) (suc n) (suc o) =
  subNat n o * (pos (suc m))                 ≡⟨ subNat-distrib-minus (suc m) n o ⟩
  subNat      (n * suc m)       (o * suc m)  ≡⟨ sym (subNat-cong-+ m (n * suc m) (o * suc m)) ⟩
  subNat (m + (n * suc m)) (m + (o * suc m)) ∎

subNat-mult-flip-negsuc : ∀ (m n o : Nat) → subNat o n * negsuc m ≡ subNat n o * pos (suc m)
subNat-mult-flip-negsuc _ zero    zero    = refl
subNat-mult-flip-negsuc _ zero    (suc _) = refl
subNat-mult-flip-negsuc _ (suc _) zero    = refl
subNat-mult-flip-negsuc m (suc n) (suc o) = subNat-mult-flip-negsuc m n o

subNat-distrib-minus-cong-+ : ∀ (m n o : Nat) → subNat o n * (pos (suc m)) ≡ subNat (m + (o * suc m)) (m + (n * suc m))
subNat-distrib-minus-cong-+ m n o = begin
  subNat o n * (pos (suc m))                 ≡⟨ subNat-distrib-minus (suc m) o n ⟩
  subNat (o * suc m) (n * suc m)             ≡⟨ sym (subNat-cong-+ m (o * suc m) (n * suc m)) ⟩
  subNat (m + (o * suc m)) (m + (n * suc m)) ∎


addInteger-assoc : ∀ (x y z : Integer) → (x + y) + z ≡ x + (y + z)
addInteger-assoc (pos zero) j k rewrite addInteger-idˡ      j  | addInteger-idˡ (j + k) = refl
addInteger-assoc i (pos zero) k rewrite addInteger-idʳ  i      | addInteger-idˡ      k  = refl
addInteger-assoc i j (pos zero) rewrite addInteger-idʳ (i + j) | addInteger-idʳ  j      = refl
addInteger-assoc (negsuc m) (negsuc n) (pos (suc o)) =
  (negsuc m + negsuc n) + pos (suc o)       ≡⟨⟩
  negsuc (suc (m + n)) + pos (suc o)        ≡⟨⟩
  subNat o (suc m + n)                      ≡⟨ cong (subNat o) (addNat-comm (suc m) n) ⟩
  subNat o (n + suc m)                      ≡⟨ subNat|x-[y+z]≡x-y-z o n m ⟩
  subNat o n + negsuc m                     ≡⟨ addInteger-comm (subNat o n) (negsuc m) ⟩
  negsuc m + subNat o n                     ≡⟨⟩
  negsuc m + (negsuc n + pos (suc o))       ∎
addInteger-assoc (negsuc m) (pos (suc n)) (pos (suc o)) =
  (negsuc m + pos (suc n)) + pos (suc o)    ≡⟨⟩
  subNat n m + pos (suc o)                  ≡⟨ subNat|x-y+z≡[x+z]-y n m o ⟩
  subNat (n + suc o) m                      ≡⟨⟩
  negsuc m + pos (suc (n + suc o))          ≡⟨⟩
  negsuc m + (pos (suc n) + pos (suc o))    ∎
addInteger-assoc (pos (suc m)) (negsuc n) (negsuc o) =
  (pos (suc m) + negsuc n) + negsuc o       ≡⟨⟩
  subNat m n + negsuc o                     ≡⟨ sym $ subNat|x-[y+z]≡x-y-z m n o ⟩
  subNat m (n + suc o)                      ≡⟨ cong (subNat m) (addNat-suc n o) ⟩
  subNat m (suc (n + o))                    ≡⟨⟩
  pos (suc m) + (negsuc (suc (n + o)))      ≡⟨⟩
  pos (suc m) + (negsuc n + negsuc o)       ∎
addInteger-assoc (pos (suc m)) (negsuc n) (pos (suc o)) =
  (pos (suc m) + negsuc n) + pos (suc o)    ≡⟨⟩
  subNat m n + pos (suc o)                  ≡⟨ subNat|x-y+[1+z]≡[1+x]+[z-y] m n o ⟩
  pos (suc m) + subNat o n                  ≡⟨⟩
  pos (suc m) + (negsuc n + pos (suc o))    ∎
addInteger-assoc (pos (suc x)) (pos (suc y)) (negsuc z) = begin
  (pos (suc x) + pos (suc y)) + negsuc z    ≡⟨⟩
  pos (suc (x + (suc y))) + negsuc z        ≡⟨ cong (_+ negsuc z) (cong pos (cong suc (addNat-suc x y))) ⟩
  pos (suc (suc (x + y))) + negsuc z        ≡⟨⟩
  subNat (suc (x + y)) z                    ≡⟨⟩
  subNat (suc  x + y)  z                    ≡⟨ subNat|[1+x+y]-z≡[1+x]+[y-z] x y z ⟩
  pos (suc x) + subNat y z                  ≡⟨⟩
  pos (suc x) + (pos (suc y)   + negsuc z)  ∎
addInteger-assoc (negsuc m) (negsuc n) (negsuc o) = cong negsuc $ cong suc $
  suc ((m + n) + o)                         ≡⟨ cong suc (addNat-assoc m n o) ⟩
  suc (m + (n + o))                         ≡⟨ sym (addNat-suc m (n + o)) ⟩
  m + (suc (n + o))                         ∎
addInteger-assoc (negsuc m) (pos (suc n)) (negsuc o) =
  (negsuc m + pos (suc n)) + negsuc o       ≡⟨⟩
  subNat n m + negsuc o                     ≡⟨ subNat|x-y+[-[1+z]]≡x-z+[-[1+y]] n m o ⟩
  subNat n o + negsuc m                     ≡⟨ addInteger-comm (subNat n o) (negsuc m) ⟩
  negsuc m + subNat n o                     ≡⟨⟩
  negsuc m + (pos (suc n) - pos (suc o))    ∎
addInteger-assoc (pos (suc m)) (pos (suc n)) (pos (suc o)) = cong pos (addNat-assoc (suc m) (suc n) (suc o))

distribute-1ˡ : ∀ (x y : Nat) → x * (1 + y) ≡ x + (y * x)
distribute-1ˡ x y = begin
  x * (suc y) ≡⟨ mulNat-suc x y ⟩
  x + (x * y) ≡⟨ cong (x +_) (mulNat-comm x y) ⟩
  x + (y * x) ∎

mulInteger-comm : ∀ (x y : Integer) → x * y ≡ y * x
mulInteger-comm (pos x)    (pos y)    = cong pos (mulNat-comm x y)
mulInteger-comm (pos x)    (negsuc y) = cong negNat $       distribute-1ˡ x y
mulInteger-comm (negsuc x) (pos y)    = cong negNat $ sym $ distribute-1ˡ y x
mulInteger-comm (negsuc x) (negsuc y) = cong pos $ cong suc $
  y + (x * (suc y)) ≡⟨ cong (y +_) (distribute-1ˡ x y) ⟩
  y + (x + (y * x)) ≡⟨ cong (y +_) (cong (x +_) (mulNat-comm y x)) ⟩
  y + (x + (x * y)) ≡⟨ sym (addNat-assoc y x (x * y)) ⟩
  (y + x) + (x * y) ≡⟨ cong (_+ x * y) (addNat-comm y x) ⟩
  (x + y) + (x * y) ≡⟨ addNat-assoc x y (x * y) ⟩
  x + (y + (x * y)) ≡⟨ cong (x +_) (sym (distribute-1ˡ y x)) ⟩
  x + (y * (suc x)) ∎

distrib-lemma : ∀ (m n o : Nat) → suc (m + ((n + o) * suc m)) ≡ (n * suc m) + (suc (m + (o * suc m)))
distrib-lemma m n o =
  suc (m + ((n + o) * suc m))             ≡⟨ cong suc (cong (m +_) (mulNat-distributeʳ-addNat (suc m) n o)) ⟩
  suc (m + ((n * suc m)   + (o * suc m))) ≡⟨⟩
   suc m + ((n * suc m)   + (o * suc m))  ≡⟨ sym (addNat-assoc (suc m) (n * suc m) (o * suc m) ) ⟩
  (suc m +  (n * suc m))  + (o * suc m)   ≡⟨ cong (_+ o * suc m) (addNat-comm (suc m) (n * suc m)) ⟩
  ((n * suc m) +  suc  m) + (o * suc m)   ≡⟨ addNat-assoc (n * suc m) (suc m) (o * suc m) ⟩
   (n * suc m) + (suc (m  + (o * suc m))) ∎

distrib-lemma2 : ∀ (m n o : Nat) → m + ((n * suc m) + (suc m + (o * suc m))) ≡ suc ((m + (n * suc m)) + (m + (o * suc m)))
distrib-lemma2 m n o =
   m + (    (n * suc m) + (suc  m + (o * suc m))) ≡⟨⟩
   m + (    (n * suc m) +  suc (m + (o * suc m))) ≡⟨ sym (addNat-assoc m (n * suc m) (suc (m + (o * suc m)))) ⟩
  (m +      (n * suc m)) + suc (m + (o * suc m))  ≡⟨ addNat-suc (m + (n * suc m)) (m + (o * suc m)) ⟩
  suc ((m + (n * suc m)) +     (m + (o * suc m))) ∎

mulInteger-distributeʳ-addInteger : ∀ (x y z : Integer) → (y + z) * x ≡ (y * x) + (z * x)
mulInteger-distributeʳ-addInteger (pos zero) j k rewrite mulInteger-zeroʳ j | mulInteger-zeroʳ k | mulInteger-zeroʳ (j + k) = refl
mulInteger-distributeʳ-addInteger i (pos zero) k rewrite addInteger-idˡ k   | mulInteger-zeroˡ i | addInteger-idˡ   (k * i) = refl
mulInteger-distributeʳ-addInteger i j (pos zero) rewrite addInteger-idʳ j   | mulInteger-zeroˡ i | addInteger-idʳ   (j * i) = refl
mulInteger-distributeʳ-addInteger (negsuc m)    (negsuc n)    (pos (suc o)) = begin
  subNat o n * negsuc m                      ≡⟨ subNat-mult-flip-negsuc m n o ⟩
  subNat n o * pos (suc m)                   ≡⟨ subNat-distrib-minus-cong-+ m o n ⟩
  subNat (m + (n * suc m)) (m + (o * suc m)) ∎
mulInteger-distributeʳ-addInteger (negsuc m)    (pos (suc n)) (pos (suc o)) = cong negsuc $ begin
  m + ((n + suc o) * suc m)                       ≡⟨ cong (m +_) (mulNat-distributeʳ-addNat (suc m) n (suc o)) ⟩
  m + (     (n * suc m) + (suc m + (o * suc m)))  ≡⟨ distrib-lemma2 m n o ⟩
  suc ((m + (n * suc m)) +     (m + (o * suc m))) ∎ -- Y
mulInteger-distributeʳ-addInteger (pos (suc m)) (negsuc n)    (negsuc o)    = cong negsuc $ begin
  m + (suc (m + ((n + o) * suc m)))               ≡⟨⟩
  m + (suc m  + ((n + o) * suc m))                ≡⟨ cong (m +_) (distrib-lemma m n o) ⟩
  m + (     (n * suc m) + (suc m + (o * suc m)))  ≡⟨ distrib-lemma2 m n o ⟩
  suc ((m + (n * suc m)) + (m + (o * suc m)))     ∎ -- Y
mulInteger-distributeʳ-addInteger (pos (suc m)) (negsuc n)    (pos (suc o)) = subNat-distrib-minus-cong-+ m n o
mulInteger-distributeʳ-addInteger (pos (suc m)) (pos (suc n)) (negsuc o)    = subNat-distrib-minus-cong-+ m o n
mulInteger-distributeʳ-addInteger (negsuc m)    (negsuc n)    (negsuc o)    = cong pos $ cong suc $
  m + (suc (m + ((n + o) * suc m)))           ≡⟨⟩
  m + (suc m  + ((n + o) * suc m))            ≡⟨ cong (m +_) (distrib-lemma m n o) ⟩
  m + ((n * suc m) + (suc m  + (o * suc m)))  ≡⟨ sym (addNat-assoc m (n * suc m) (suc m + (o * suc m))) ⟩
  (m + (n * suc m)) + (suc (m + (o * suc m))) ∎ -- X
mulInteger-distributeʳ-addInteger (negsuc m)    (pos (suc n)) (negsuc o)    =
  subNat n o * negsuc m                      ≡⟨ subNat-mult-flip-negsuc m o n ⟩
  subNat o n * pos (suc m)                   ≡⟨ subNat-distrib-minus-cong-+ m n o ⟩
  subNat (m + (o * suc m)) (m + (n * suc m)) ∎
mulInteger-distributeʳ-addInteger (pos (suc m)) (pos (suc n)) (pos (suc o)) = cong pos $ cong suc $
  m + ((n + suc o) * suc m)                   ≡⟨ cong (m +_) (mulNat-distributeʳ-addNat (suc m) n (suc o)) ⟩
  m + ((n * suc m) + (suc m  + (o * suc m)))  ≡⟨ sym (addNat-assoc m (n * suc m) (suc m + (o * suc m))) ⟩
  (m + (n * suc m)) + (suc m  + (o * suc m))  ≡⟨⟩
  (m + (n * suc m)) + (suc (m + (o * suc m))) ∎ -- X

mulInteger-distributeˡ-addInteger : ∀ (x y z : Integer) → x * (y + z) ≡ (x * y) + (x * z)
mulInteger-distributeˡ-addInteger x y z
  -- This proof works the very same as addNat-distributeˡ-mulNat.
  rewrite (mulInteger-comm x (y + z)) -- makes or goal become: (y + z) * x ≡ (x * y) + (x * z)
  rewrite (mulInteger-comm x y)       -- makes or goal become: (y + z) * x ≡ (y * x) + (x * z)
  rewrite (mulInteger-comm x z)       -- makes or goal become: (y + z) * x ≡ (y * x) + (z * x)
  = mulInteger-distributeʳ-addInteger x y z

mulInteger-assoc-lemma-2 : ∀ (m n o : Nat) → (n + m * suc n) * suc o ≡ (n * suc o) + (m * suc (o + (n * suc o)))
mulInteger-assoc-lemma-2 m n o =            begin
  (n + (m * suc n)) * (suc o)               ≡⟨ mulNat-distributeʳ-addNat (suc o) n (m * suc n) ⟩
  (n * (suc o)) + ((m * suc n) * (suc o))   ≡⟨ cong (n * suc o +_) (mulNat-assoc m (suc n) (suc o)) ⟩
  (n * suc o) + (m * suc (o + (n * suc o))) ∎

mulInteger-assoc-lemma : ∀ (m n o : Nat)
  → o + ((n + m * suc n) * suc o) ≡ (o + (n * suc o)) + (m * suc (o + (n * suc o)))
mulInteger-assoc-lemma m n o =                      begin
    o + ((n + m * suc n) * suc o)                   ≡⟨ cong (o +_) (mulInteger-assoc-lemma-2 m n o) ⟩
    o + ((n * suc o) + (m * suc (o + (n * suc o)))) ≡⟨ sym (addNat-assoc o (n * suc o) (m * suc (o + (n * suc o)))) ⟩
    (o + (n * suc o)) + (m * suc (o + (n * suc o))) ∎

mulInteger-assoc : ∀ (x y z : Integer) → (x * y) * z ≡ x * (y * z)
mulInteger-assoc (pos zero) j k rewrite mulInteger-zeroˡ j | mulInteger-zeroˡ k | mulInteger-zeroˡ (j * k) = refl
mulInteger-assoc i (pos zero) k rewrite mulInteger-zeroʳ i | mulInteger-zeroˡ k | mulInteger-zeroʳ i       = refl
mulInteger-assoc i j (pos zero) rewrite mulInteger-zeroʳ j | mulInteger-zeroʳ i | mulInteger-zeroʳ (i * j) = refl
mulInteger-assoc (negsuc m)    (negsuc n)    (pos (suc o)) = cong pos (cong suc (mulInteger-assoc-lemma m n o))
mulInteger-assoc (negsuc m)    (pos (suc n)) (pos (suc o)) = cong negsuc        (mulInteger-assoc-lemma m n o)
mulInteger-assoc (pos (suc m)) (negsuc n)    (negsuc o)    = cong pos (cong suc (mulInteger-assoc-lemma m n o))
mulInteger-assoc (pos (suc m)) (negsuc n)    (pos (suc o)) = cong negsuc        (mulInteger-assoc-lemma m n o)
mulInteger-assoc (pos (suc m)) (pos (suc n)) (negsuc o)    = cong negsuc        (mulInteger-assoc-lemma m n o)
mulInteger-assoc (negsuc m)    (negsuc n)    (negsuc o)    = cong negsuc        (mulInteger-assoc-lemma m n o)
mulInteger-assoc (negsuc m)    (pos (suc n)) (negsuc o)    = cong pos (cong suc (mulInteger-assoc-lemma m n o))
mulInteger-assoc (pos (suc m)) (pos (suc n)) (pos (suc o)) = cong pos (cong suc (mulInteger-assoc-lemma m n o))

instance
  iLawfulNumInteger : IsLawfulNum Integer
  iLawfulNumInteger .IsLawfulNum.+-assoc = addInteger-assoc
  iLawfulNumInteger .IsLawfulNum.+-comm = addInteger-comm
  iLawfulNumInteger .IsLawfulNum.+-idˡ x = addInteger-idˡ x
  iLawfulNumInteger .IsLawfulNum.+-idʳ x = addInteger-idʳ x
  iLawfulNumInteger .IsLawfulNum.neg-inv x = n-n≡0-Integer x
  iLawfulNumInteger .IsLawfulNum.*-assoc = mulInteger-assoc
  iLawfulNumInteger .IsLawfulNum.*-idˡ x = mulInteger-idˡ x
  iLawfulNumInteger .IsLawfulNum.*-idʳ x = mulInteger-idʳ x
  iLawfulNumInteger .IsLawfulNum.distributeˡ = mulInteger-distributeˡ-addInteger
  iLawfulNumInteger .IsLawfulNum.distributeʳ = mulInteger-distributeʳ-addInteger
