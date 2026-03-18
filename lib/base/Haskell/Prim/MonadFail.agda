module Haskell.Prim.MonadFail where

open import Haskell.Prim
open import Haskell.Prim.String
open import Haskell.Prim.Monad
open import Haskell.Prim.Maybe
open import Haskell.Prim.IO


--------------------------------------------------------------------------------
-- MonadFail

record MonadFail (m : Type → Type) : Type₁ where
  field
    fail : String → m a
    overlap ⦃ super ⦄ : Monad m

open MonadFail ⦃...⦄ public
{-# COMPILE AGDA2HS MonadFail existing-class #-}

instance
  MonadFailList : MonadFail List
  MonadFailList .fail _ = []

  MonadFailMaybe : MonadFail Maybe
  MonadFailMaybe .fail _ = Nothing

  iMonadFailIO : MonadFail IO
  iMonadFailIO .fail = failIO
