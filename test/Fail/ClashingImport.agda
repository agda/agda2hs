module Fail.ClashingImport where

open import Importee
open import OtherImportee

testFoo : Foo
testFoo = MkFoo
{-# COMPILE AGDA2HS testFoo #-}

otherFoo : OtherFoo
otherFoo = MkFoo
{-# COMPILE AGDA2HS otherFoo #-}
