module TypeOperatorImport where

{-# FOREIGN AGDA2HS {-# LANGUAGE TypeOperators #-} #-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import TypeOperatorExport

test1 : ⊤ < Bool
test1 = tt
{-# COMPILE AGDA2HS test1 #-}

test2 : Bool -> Bool -> ⊤ *** Bool
test2 b1 b2 = tt :*: (b1 &&& b2)
{-# COMPILE AGDA2HS test2 #-}
