module ModuleParametersImports where

open import Haskell.Prelude
open import ModuleParameters Bool (λ _ → Nat)

scope : Scope
scope = unbind (Bind True 3 (Bind False 2 Empty))
{-# COMPILE AGDA2HS scope #-}


