module DelayMonad where

open import Haskell.Prelude
open import Haskell.Extra.Delay

open import Agda.Builtin.Size

-- The `Delay` monad is also a transparent monad, i.e. its class methods are
-- compiled to the identity monad.
pureDelay : Delay Nat ∞
pureDelay = return 1
{-# COMPILE AGDA2HS pureDelay #-}

mapDelay : Delay Nat ∞ → Delay Nat ∞
mapDelay = fmap (_+ 1)
{-# COMPILE AGDA2HS mapDelay #-}

bindDelay' : Delay Nat ∞ → Delay Nat ∞
bindDelay' m = m >>= λ x → return (x + 1)
{-# COMPILE AGDA2HS bindDelay' #-}
