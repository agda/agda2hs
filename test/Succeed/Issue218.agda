
module Issue218 where

open import Haskell.Prelude
open import Agda2Hs.Extra.Erase
open import Agda2Hs.Extra.Refinement

module _ (@0 n : Int) where

  foo : {{Singleton n}} → ∃ Int (_≡ n)
  foo {{sing n}} = n ⟨ refl ⟩

  {-# COMPILE AGDA2HS foo #-}

bar : ∃ Int (_≡ 42)
bar = foo _

{-# COMPILE AGDA2HS bar #-}
