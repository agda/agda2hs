module Haskell.Law.Applicative.FromMonad where

open import Haskell.Prim

open import Haskell.Prim.Applicative
open import Haskell.Prim.Functor
open import Haskell.Prim.Monad

open import Haskell.Law.Applicative.Def
open import Haskell.Law.Monad.Def as Monad
open import Haskell.Law.Equality
open import Haskell.Law.Functor
open import Haskell.Law.Functor.FromMonad

-------------------------------------------------------------------------------
-- Prove the Applicative laws from the Monad laws

--
prop-PreLawfulMonad→IsLawfulApplicative
  : ∀ ⦃ _ : Monad m ⦄ ⦃ _ : PreLawfulMonad m ⦄
  → IsLawfulApplicative m
--
prop-PreLawfulMonad→IsLawfulApplicative {m} = record
    { super = prop-PreLawfulMonad→IsLawfulFunctor
    ; identity = midentity
    ; composition = mcomposition
    ; homomorphism = mhomomorphism
    ; interchange = minterchange
    ; functor = mfunctor
    }
  where
    midentity : ∀ {a} (ma : m a) → (pure id <*> ma) ≡ ma
    midentity {a} ma
      rewrite def-pure-return (id {a})
      | def-<*>->>= (return id) ma
      = begin
        return id >>= (λ f → ma >>= (λ x → return (f x)))
      ≡⟨ Monad.leftIdentity _ _ ⟩
        ma >>= (λ x → return (id x))
      ≡⟨ Monad.rightIdentity _ ⟩
        ma
      ∎

    mfunctor : ∀ {a b} (f : a → b) (u : m a) → fmap f u ≡ (pure f <*> u)
    mfunctor f u = begin
        fmap f u
      ≡⟨ Monad.def-fmap->>= _ _ ⟩
        (do x ← u; return (f x))
      ≡⟨ sym (Monad.leftIdentity _ _) ⟩
        (do f' ← return f; x ← u; return (f' x))
      ≡⟨ cong (λ o → o >>= _) (sym (def-pure-return _)) ⟩
        (do f' ← pure f; x ← u; return (f' x))
      ≡⟨ sym (def-<*>->>= _ _) ⟩
        pure f <*> u
      ∎

    mcomposition
      : ∀ {a b c} (u : m (b → c)) (v : m (a → b)) (w : m a)
      → (pure _∘_ <*> u <*> v <*> w) ≡ (u <*> (v <*> w))
    mcomposition u v w
      = begin
        pure _∘_ <*> u <*> v <*> w
      ≡⟨ cong (λ o → o <*> u <*> v <*> w) (def-pure-return _∘_) ⟩
        return _∘_ <*> u <*> v <*> w
      ≡⟨ cong (λ o → o <*> v <*> w) (def-<*>->>= _ _ ) ⟩
        (do comp ← return _∘_; g ← u; return (comp g)) <*> v <*> w
      ≡⟨ cong (λ o → o <*> v <*> w) (Monad.leftIdentity _ _) ⟩
        (do g ← u; return (_∘_ g)) <*> v <*> w
      ≡⟨ cong (λ o → o <*> w) (def-<*>->>= _ _ ) ⟩
        (do g' ← (do g ← u; return (_∘_ g)); f ← v; return (g' f)) <*> w
      ≡⟨ cong (λ o → o <*> w) (sym (Monad.associativity u _ _)) ⟩
        (do g ← u; g' ← return (_∘_ g); f ← v; return (g' f)) <*> w
      ≡⟨ cong (λ o → o <*> w) (cong-monad u (λ g → Monad.leftIdentity _ _)) ⟩
        (do g ← u; f ← v; return (g ∘ f)) <*> w
      ≡⟨ def-<*>->>= _ _ ⟩
        (do gf ← (do g ← u; f ← v; return (g ∘ f)); x ← w; return (gf x))
      ≡⟨ sym (Monad.associativity u _ _) ⟩
        (do g ← u; gf ← (do f ← v; return (g ∘ f)); x ← w; return (gf x))
      ≡⟨ cong-monad u (λ g → sym (Monad.associativity v _ _)) ⟩
        (do g ← u; do f ← v; gf ← return (g ∘ f); x ← w; return (gf x))
      ≡⟨ cong-monad u (λ g → cong-monad v (λ f → Monad.leftIdentity _ _)) ⟩
        (do g ← u; f ← v; x ← w; return (g (f x)))
      ≡⟨ cong-monad u (λ g → cong-monad v λ f → cong-monad w (λ x → sym (Monad.leftIdentity _ _))) ⟩
        (do g ← u; f ← v; x ← w; y ← return (f x); return (g y))
      ≡⟨ cong-monad u (λ g → cong-monad v λ x → Monad.associativity _ _ _) ⟩
        (do g ← u; f ← v; y ← (do x ← w; return (f x)); return (g y))
      ≡⟨ cong-monad u (λ g → Monad.associativity _ _ _) ⟩
        (do g ← u; y ← (do f ← v; x ← w; return (f x)); return (g y))
      ≡⟨ sym (def-<*>->>= _ _) ⟩
        u <*> (do f ← v; x ← w; return (f x))
      ≡⟨ cong (λ o → u <*> o) (sym (def-<*>->>= _ _)) ⟩
        u <*> (v <*> w)
      ∎

    mhomomorphism
      : ∀ {a b} (f : a → b) (x : a)
      → (pure {m} f <*> pure x) ≡ pure (f x)
    mhomomorphism f x = begin
        pure {m} f <*> pure x
      ≡⟨ cong₂ (_<*>_) (def-pure-return f) (def-pure-return x) ⟩
        return {m} f <*> return x
      ≡⟨ def-<*>->>= _ _ ⟩
        (do f' ← return f; x' ← return x; return (f' x'))
      ≡⟨ Monad.leftIdentity _ _ ⟩
        (do x' ← return x; return (f x'))
      ≡⟨ Monad.leftIdentity _ _ ⟩
        return (f x)
      ≡⟨ sym (def-pure-return _) ⟩
        pure (f x)
      ∎

    minterchange
      : ∀ {a b} (u : m (a → b)) (y : a)
      → (u <*> pure y) ≡ (pure (_$ y) <*> u)
    minterchange u y = begin
        u <*> pure y
      ≡⟨ cong (u <*>_) (def-pure-return _) ⟩
        u <*> return y
      ≡⟨ def-<*>->>= _ _ ⟩
        (do f ← u; y' ← return y; return (f y'))
      ≡⟨ cong-monad u (λ f → Monad.leftIdentity y _) ⟩
        (do f ← u; return (f y))
      ≡⟨ sym (Monad.leftIdentity _ _) ⟩
        (do y'' ← return (_$ y); f ← u; return (y'' f))
      ≡⟨ sym (def-<*>->>= _ _) ⟩
        return (_$ y) <*> u
      ≡⟨ sym (cong (_<*> u) (def-pure-return _)) ⟩
        pure (_$ y) <*> u
      ∎
