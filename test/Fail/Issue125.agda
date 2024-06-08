module Fail.Issue125 where

data A (a : Set) : Set where
  ACtr : a -> A a

{-# COMPILE AGDA2HS A #-}

data B : Set where
  ACtr : B

{-# COMPILE AGDA2HS B #-}

data C : Set where
  Ca : C

{-# COMPILE AGDA2HS C #-}