open import Haskell.Prelude
open import Importee
open import OtherImportee using ( MkFoo )
import QualifiedImportee as Qually

bar : Int
bar = foo

{-# COMPILE AGDA2HS bar #-}

otherBar : Int
otherBar = anotherFoo

{-# COMPILE AGDA2HS otherBar #-}

thirdBar : Int
thirdBar = Qually.foo

{-# COMPILE AGDA2HS thirdBar #-}

baz : Int
baz = 21 !# 21

{-# COMPILE AGDA2HS baz #-}

otherBaz : Int
otherBaz = 2 Qually.!# 2

{-# COMPILE AGDA2HS otherBaz #-}

myFoo : Foo
myFoo = MkFoo -- This is MkFoo from Importee, NOT from OtherImportee!!

{-# COMPILE AGDA2HS myFoo #-}

myOtherFoo : Foo
myOtherFoo = doTheFoo

{-# COMPILE AGDA2HS myOtherFoo #-}

thirdFoo : Qually.Foo
thirdFoo = Qually.doTheFoo

{-# COMPILE AGDA2HS thirdFoo #-}
