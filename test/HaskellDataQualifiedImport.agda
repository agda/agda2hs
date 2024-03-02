{-# OPTIONS --erasure #-}

module HaskellDataQualifiedImport where

open import Agda.Builtin.Int
import Haskell.Data.Map as Map

map : Map.Map Int Int
map = Map.empty
{-# COMPILE AGDA2HS map #-}
