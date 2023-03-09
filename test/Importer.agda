open import Haskell.Prelude

{-# FOREIGN AGDA2HS
-- ** simple imports (possibly with transitive dependencies)
#-}

open import Importee
open import OtherImportee using (MkFoo)

bar : Int
bar = foo
{-# COMPILE AGDA2HS bar #-}

anotherBar : Int
anotherBar = anotherFoo
{-# COMPILE AGDA2HS anotherBar #-}

baz : Int
baz = 21 !# 21
{-# COMPILE AGDA2HS baz #-}

mkFoo : Foo
mkFoo = MkFoo -- This is MkFoo from Importee, NOT from OtherImportee!!
{-# COMPILE AGDA2HS mkFoo #-}

fooable : Foo
fooable = doTheFoo
{-# COMPILE AGDA2HS fooable #-}

{-# FOREIGN AGDA2HS
-- ** interplay with class default methods
#-}

defaultBar : Foo
defaultBar = defaultFoo
{-# COMPILE AGDA2HS defaultBar #-}

{-# FOREIGN AGDA2HS
-- ** interplay with methods of existing class
#-}

testFoldMap : List Nat → List Nat
testFoldMap = foldMap _∷_ []
{-# COMPILE AGDA2HS testFoldMap #-}

{-# FOREIGN AGDA2HS
-- ** interplay with default methods of existing class
#-}

testFoldr : List Nat → Nat
testFoldr = foldr (λ _ x → x) 0
{-# COMPILE AGDA2HS testFoldr #-}
