open import Haskell.Prelude
open import Importee
open import OtherImportee using ( MkFoo )

bar : Int
bar = foo

{-# COMPILE AGDA2HS bar #-}

baz : Int
baz = 21 !# 21

{-# COMPILE AGDA2HS baz #-}

myFoo : Foo
myFoo = MkFoo -- This is MkFoo from Importee, NOT from OtherImportee!!

{-# COMPILE AGDA2HS myFoo #-}

myOtherFoo : Foo
myOtherFoo = doTheFoo

{-# COMPILE AGDA2HS myOtherFoo #-}

otherBar : Int
otherBar = anotherFoo

{-# COMPILE AGDA2HS otherBar #-}
