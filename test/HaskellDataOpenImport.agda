{-# OPTIONS --erasure #-}

module HaskellDataOpenImport where

open import Agda.Builtin.Int
open import Haskell.Data.Map

map : Map Int Int
map = empty
{-# COMPILE AGDA2HS map #-}
