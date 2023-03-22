module Haskell.Law.Monad.Def where

open import Haskell.Prim

open import Haskell.Prim.Monad

record IsLawfulMonad (func : Set → Set) ⦃ iMonadF : Monad func ⦄ : Set₁ where
  field
    -- Left identity: return a >>= k = k a
    leftIdentity : {a : Set} → (a' : a) → (k : a → func b) → ((return a') >>= k) ≡ k a'

    -- Right identity: m >>= return = m
    rightIdentity : {a : Set} → (ma : func a) → (ma >>= (return)) ≡ ma

    -- Associativity: m >>= (\x -> k x >>= h) = (m >>= k) >>= h
    associativity : {a b c : Set} → (ma : func a) → (f : a → func b) → (g : b → func c)
      → (ma >>= (λ x → f x >>= g)) ≡ ((ma >>= f) >>= g)

    -- pure = return
    -- m1 <*> m2 = m1 >>= (\x1 -> m2 >>= (\x2 -> return (x1 x2)))

    -- fmap f xs  =  xs >>= return . f
    -- (>>) = (*>)
        
open IsLawfulMonad ⦃ ... ⦄ public
 
instance
  postulate iLawfulMonadFun : IsLawfulMonad (λ b → a → b)
 