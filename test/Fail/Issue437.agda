module Fail.Issue437 where

data Indexed : (a : Set) → Set₁ where
    MkIndexed : { a : Set } → Indexed a
{-# COMPILE AGDA2HS Indexed #-}
