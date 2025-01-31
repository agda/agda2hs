module Fail.Issue125 where

open import Haskell.Prim using (Type)

data A (a : Type) : Type where
  ACtr : a -> A a

{-# COMPILE AGDA2HS A #-}

data B : Type where
  ACtr : B

{-# COMPILE AGDA2HS B #-}

data C : Type where
  Ca : C

{-# COMPILE AGDA2HS C #-}
