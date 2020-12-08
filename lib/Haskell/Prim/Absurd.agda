
module Haskell.Prim.Absurd where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_; absurd to absurdP)
open import Agda.Builtin.Equality

private

  pattern vArg x = arg (arg-info visible relevant) x

  variable
    a b : Set

  _$_ : (a → b) → a → b
  f $ x = f x

  refute : Nat → Term
  refute i = def (quote _$_) (vArg (pat-lam (absurd-clause (vArg absurdP ∷ []) ∷ []) []) ∷ vArg (var i []) ∷ [])

  tryRefute : Nat → Term → TC ⊤
  tryRefute 0       _    = typeError (strErr "No variable of empty type found in the context" ∷ [])
  tryRefute (suc n) hole = catchTC (unify hole (refute n)) (tryRefute n hole)

  len : List a → Nat
  len []       = 0
  len (_ ∷ xs) = suc (len xs)

absurd : Term → TC ⊤
absurd hole = do
  Γ ← getContext
  tryRefute (len Γ) hole
