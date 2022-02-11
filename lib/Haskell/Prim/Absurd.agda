
module Haskell.Prim.Absurd where

open import Haskell.Prim

open import Agda.Builtin.Reflection renaming (bindTC to _>>=_; absurd to absurdP)

private

  pattern vArg x = arg (arg-info visible (modality relevant quantity-ω)) x

  refute : Natural → Term
  refute i = def (quote _$_) ( vArg (pat-lam (absurd-clause [] (vArg (absurdP 0) ∷ []) ∷ []) [])
                             ∷ vArg (var i []) ∷ [])

  tryRefute : Natural → Term → TC ⊤
  tryRefute 0       _    = typeError (strErr "No variable of empty type found in the context" ∷ [])
  tryRefute (suc n) hole = catchTC (unify hole (refute n)) (tryRefute n hole)

absurd : Term → TC ⊤
absurd hole = do
  Γ ← getContext
  tryRefute (lengthNat Γ) hole
