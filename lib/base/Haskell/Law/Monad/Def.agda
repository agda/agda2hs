module Haskell.Law.Monad.Def where

open import Haskell.Prim

open import Haskell.Prim.Applicative
open import Haskell.Prim.Functor
open import Haskell.Prim.Monad
open import Haskell.Prim.Monoid
open import Haskell.Prim.Tuple

open import Haskell.Law.Applicative
open import Haskell.Law.Equality
open import Haskell.Law.Extensionality

-- Helper function: Substitution in the second argument of '(>>=)'.
cong-monad
  : ∀ ⦃ _ : Monad m ⦄ (mx : m a) {f g : a → m b}
  → (∀ x → f x ≡ g x)
  → (do x ← mx; f x) ≡ (do x ← mx; g x)
--
cong-monad mx {f} {g} eq = cong (mx >>=_) (ext eq)

-------------------------------------------------------------------------------
-- Monad laws
--
-- `PreLawfulMonad` contains all laws that we expect a 'Monad' to satisfy,
-- except that we do not yet require that the superclasses are themselves
-- lawful, this is deferred to `IsLawfulMonad`.
-- The lawfulness of the superclasses can be proven from `PreLawfulMonad`.

record PreLawfulMonad (m : Type → Type) ⦃ _ : Monad m ⦄ : Type₁ where
  field
    -- The three monad laws
    leftIdentity  : ∀ {a} (x : a) (k : a → m b)
      → (return x >>= k) ≡ k x

    rightIdentity : ∀ {a} (ma : m a)
      → (ma >>= return) ≡ ma

    associativity : ∀ {a b c} (ma : m a) (f : a → m b) (g : b → m c)
      → (ma >>= (λ x → f x >>= g)) ≡ ((ma >>= f) >>= g)

    -- Default functions
    def->>->>= : ∀ {a b} (ma : m a) (mb : m b)
      → ma >> mb ≡ ma >>= (λ x → mb)

    def-pure-return : ∀ {a} (x : a)
      → pure {m} x ≡ return x

    -- Superclass functions
    def-fmap->>= : ∀ {a b} (f : a → b) (ma : m a)
      → fmap f ma ≡ ma >>= (return ∘ f)

    def-<*>->>= : ∀ {a b} (mab : m (a → b)) (ma : m a)
      → (mab <*> ma) ≡ (mab >>= (λ f → (ma >>= (λ x → return (f x)))))

open PreLawfulMonad ⦃ ... ⦄ public

-- All laws together
record IsLawfulMonad (m : Type → Type) ⦃ _ : Monad m ⦄ : Type₁ where
  field
    overlap ⦃ applicative ⦄ : IsLawfulApplicative m
    overlap ⦃ monad ⦄       : PreLawfulMonad m

open IsLawfulMonad ⦃ ... ⦄ public

-------------------------------------------------------------------------------
-- postulated monad laws, to be proven

instance postulate
  iLawfulMonadFun : IsLawfulMonad (λ b → a → b)

  iLawfulMonadTuple₂ : ⦃ Monoid a ⦄ → Monad (a ×_)

  iLawfulMonadTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → Monad (a × b ×_)
