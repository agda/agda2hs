
open import Haskell.Prim hiding (f)

-- Names of definitions inside a module should not be qualified in the
-- generated Haskell code!

module _ where

module A where

  data D : Type where
    C : D
  {-# COMPILE AGDA2HS D #-}

  f : D → D
  f C = C
  {-# COMPILE AGDA2HS f #-}

  g : D
  g = h
    where
      h : D
      h = C
  {-# COMPILE AGDA2HS g #-}

open A public
