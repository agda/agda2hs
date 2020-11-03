
module Tuples where

open import Haskell.Prelude

swap : ⟨ a × b ⟩ → ⟨ b × a ⟩
swap ⟨ a , b ⟩ = ⟨ b , a ⟩

{-# COMPILE AGDA2HS swap #-}

unit2unit : ⊤ → Tuple []
unit2unit tt = []

{-# COMPILE AGDA2HS unit2unit #-}
