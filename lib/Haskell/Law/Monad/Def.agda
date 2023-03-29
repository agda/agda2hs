module Haskell.Law.Monad.Def where

open import Haskell.Prim

open import Haskell.Prim.Applicative
open import Haskell.Prim.Functor
open import Haskell.Prim.Monad
open import Haskell.Prim.Monoid
open import Haskell.Prim.Tuple

open import Haskell.Law.Applicative

record IsLawfulMonad (F : Set → Set) ⦃ iMonadF : Monad F ⦄ : Set₁ where
  field
    overlap ⦃ super ⦄ : IsLawfulApplicative F

    -- Left identity: return a >>= k = k a
    leftIdentity : {a : Set} → (a' : a) (k : a → F b) → ((return a') >>= k) ≡ k a'

    -- Right identity: m >>= return = m
    rightIdentity : {a : Set} → (ma : F a) → (ma >>= return) ≡ ma

    -- Associativity: m >>= (\x -> k x >>= h) = (m >>= k) >>= h
    associativity : {a b c : Set} → (ma : F a) (f : a → F b) (g : b → F c)
      → (ma >>= (λ x → f x >>= g)) ≡ ((ma >>= f) >>= g)

    -- pure = return
    pureIsReturn : (a' : a) → pure a' ≡ (Monad.return iMonadF a')
    -- m1 <*> m2 = m1 >>= (\x1 -> m2 >>= (\x2 -> return (x1 x2)))
    sequence2bind : {a b : Set} → (mab : F (a → b)) (ma : F a)
      → (mab <*> ma) ≡ (mab >>= (λ x1 → (ma >>= (λ x2 → return (x1 x2)))))

    -- fmap f xs  =  xs >>= return . f
    fmap2bind : {a b : Set} → (f : a → b) (ma : F a)
      → fmap f ma ≡ (ma >>= (return ∘ f))
    -- (>>) = (*>)
    rSequence2rBind : (ma : F a) → (mb : F b) → (ma *> mb) ≡ (ma >> mb)

open IsLawfulMonad ⦃ ... ⦄ public

instance postulate
  iLawfulMonadFun : IsLawfulMonad (λ b → a → b)

  iLawfulMonadTuple₂ : ⦃ Monoid a ⦄ → Monad (a ×_)

  iLawfulMonadTuple₃ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → Monad (a × b ×_)

  iLawfulMonadTuple₄ : ⦃ Monoid a ⦄ → ⦃ Monoid b ⦄ → ⦃ Monoid c ⦄ →
    Monad (λ d → Tuple (a ∷ b ∷ c ∷ d ∷ []))

