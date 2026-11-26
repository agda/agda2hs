{-# LANGUAGE RankNTypes #-}
module CompileToAlphaDataTarget
  (Target(..))
where

data Target a = MkTarget (forall x . x -> x) a

