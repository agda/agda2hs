open import Haskell.Prelude

{-# FOREIGN AGDA2HS
-- ** conflicting imports are all replaced with the "smallest" qualifier
--   * the characters are ordered based on their ASCII value (i.e. capitals first)
--   * the order of the imports in the file does not matter
--   * the scope-checker has already replaced previous definitions in the file
#-}

import QualifiedImportee as C

requalBar : Int
requalBar = C.foo
{-# COMPILE AGDA2HS requalBar #-}

import QualifiedImportee as A

requalBaz : Int
requalBaz = 2 A.!# 2
{-# COMPILE AGDA2HS requalBaz #-}

requalFooable : A.Foo
requalFooable = C.doTheFoo
{-# COMPILE AGDA2HS requalFooable #-}

import QualifiedImportee as B

requalDefaultBar : B.Foo
requalDefaultBar = B.defaultFoo
{-# COMPILE AGDA2HS requalDefaultBar #-}

{-# FOREIGN AGDA2HS
-- ** qualifying an open'ed module has no effect
#-}
import Haskell.Prelude as Pre
import OtherImportee as Other
open import OtherImportee using (OtherFoo)

T = Pre.Int
{-# COMPILE AGDA2HS T #-}

otherFoo : OtherFoo
otherFoo = Other.MkFoo -- this qualification is not retained
{-# COMPILE AGDA2HS otherFoo #-}
