module Fail.BadBuiltinImport where

import Agda.Builtin.Word

{-# FOREIGN AGDA2HS
import RandomModule (Word64)
import AlsoNotRight (foo, Word64(..))
import AsConstructor (D(Word64))
#-}
