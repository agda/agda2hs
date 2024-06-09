module TypeOperatorImport where

{-# FOREIGN AGDA2HS {-# LANGUAGE TypeOperators #-} #-}

open import Haskell.Prelude hiding (_<_)
open import TypeOperatorExport

test1 : ⊤ < Bool
test1 = tt
{-# COMPILE AGDA2HS test1 #-}

test2 : Bool -> Bool -> ⊤ *** Bool
test2 b1 b2 = ((tt :*:_) ∘ not) (b1 &&& b2)
{-# COMPILE AGDA2HS test2 #-}
