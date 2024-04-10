module RuntimeCheckAutoImport where

open import Haskell.Prelude

simpleFun : (x : Nat) ⦃@0 _ : IsTrue (x > 0)⦄ → Nat
simpleFun _ = 0
{-# COMPILE AGDA2HS simpleFun #-}
