open import Haskell.Prelude

{-# FOREIGN AGDA2HS
-- ** simple qualification
#-}

import Importee

simpqualBar : Int
simpqualBar = Importee.foo
{-# COMPILE AGDA2HS simpqualBar #-}

simpfoo : Importee.Foo
simpfoo = Importee.Foo.MkFoo
{-# COMPILE AGDA2HS simpfoo #-}

{-# FOREIGN AGDA2HS
-- ** qualified imports
#-}

import QualifiedImportee as Qually

qualBar : Int
qualBar = Qually.foo
{-# COMPILE AGDA2HS qualBar #-}

qualBaz : Int
qualBaz = 2 Qually.!# 2
{-# COMPILE AGDA2HS qualBaz #-}

qualFooable : Qually.Foo
qualFooable = Qually.doTheFoo
{-# COMPILE AGDA2HS qualFooable #-}

qualDefaultBar : Qually.Foo
qualDefaultBar = Qually.defaultFoo
{-# COMPILE AGDA2HS qualDefaultBar #-}

Foo : Set
Foo = Importee.Foo
{-# COMPILE AGDA2HS Foo #-}
