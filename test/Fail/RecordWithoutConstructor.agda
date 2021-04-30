module Fail.RecordWithoutConstructor where

record Test (a : Set) : Set where
  field
    one : a

{-# COMPILE AGDA2HS Test #-}
