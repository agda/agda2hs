module Haskell.Law.Monad.Def where

open import Haskell.Prim

open import Haskell.Prim.Applicative
open import Haskell.Prim.Functor
open import Haskell.Prim.Monad

open import Haskell.Law.Applicative

record IsLawfulMonad (func : Set → Set) ⦃ iMonadF : Monad func ⦄ : Set₁ where
  field
    overlap ⦃ super ⦄ : IsLawfulApplicative func

    -- Left identity: return a >>= k = k a
    leftIdentity : {a : Set} → (a' : a) → (k : a → func b) → ((return a') >>= k) ≡ k a'

    -- Right identity: m >>= return = m
    rightIdentity : {a : Set} → (ma : func a) → (ma >>= (return)) ≡ ma

    -- Associativity: m >>= (\x -> k x >>= h) = (m >>= k) >>= h
    associativity : {a b c : Set} → (ma : func a) → (f : a → func b) → (g : b → func c)
      → (ma >>= (λ x → f x >>= g)) ≡ ((ma >>= f) >>= g)

    -- pure = return
    pureIsReturn : (a' : a) → pure a' ≡ (Monad.return iMonadF a')
    -- m1 <*> m2 = m1 >>= (\x1 -> m2 >>= (\x2 -> return (x1 x2)))
    sequence2bind : {a b : Set} → (mab : func (a → b)) → (ma : func a)
      → (mab <*> ma) ≡ (mab >>= (λ x1 → (ma >>= (λ x2 → return (x1 x2)))))

    -- fmap f xs  =  xs >>= return . f
    fmap2bind : {a b : Set} → (f : a → b) → (ma : func a)
      → fmap f ma ≡ (ma >>= (return ∘ f))
    -- (>>) = (*>)
    rSequence2rBind : (ma : func a) → (mb : func b) → (ma *> mb) ≡ (ma >> mb)

open IsLawfulMonad ⦃ ... ⦄ public

instance
  postulate iLawfulMonadFun : IsLawfulMonad (λ b → a → b)

