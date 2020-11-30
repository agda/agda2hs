
module Issue14 where

open import Haskell.Prelude

-- Wrong name for shadowed lambda
constid : a → b → b
constid x = λ x → x

{-# COMPILE AGDA2HS constid #-}

sectionTest₁ : Nat → Nat → Nat
sectionTest₁ n = _+ n

sectionTest₂ : Nat → Nat → Nat
sectionTest₂ section = _+ section

{-# COMPILE AGDA2HS sectionTest₁ #-}
{-# COMPILE AGDA2HS sectionTest₂ #-}
