{-# LANGUAGE GADTs #-}
module CompileToGadtTarget
  (Res(..))
where

data Res a where
    MkRes :: a -> Res a

