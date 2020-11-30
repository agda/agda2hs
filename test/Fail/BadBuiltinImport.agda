module Fail.BadBuiltinImport where

import Agda.Builtin.Nat

{-# FOREIGN AGDA2HS
import RandomModule (Natural)
import AlsoNotRight (foo, Natural(..))
import AsConstructor (D(Natural))
#-}
