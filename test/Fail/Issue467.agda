{-# OPTIONS --erasure #-}

module Issue467 where

open import Haskell.Prelude

idFun : {A : Set} → A → A
idFun x = x
{-# COMPILE AGDA2HS idFun #-}
