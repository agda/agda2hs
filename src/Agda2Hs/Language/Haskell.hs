-- | Haskell syntax, parsing, pretty printing.
--
-- This module contains those elements of the Haskell language
-- that are needed by Agda2hs.
--
-- We are mainly re-exporting @haskell-src-exts@.
module Agda2Hs.Language.Haskell
  ( module Language.Haskell.Exts.Build
  , module Language.Haskell.Exts.ExactPrint
  , module Language.Haskell.Exts.Extension
  , module Language.Haskell.Exts.Parser
  , module Language.Haskell.Exts.Pretty
  , module Language.Haskell.Exts.Syntax
  , module Agda2Hs.Language.Haskell.Utils
  ) where

import Agda2Hs.Language.Haskell.Utils

import Language.Haskell.Exts.Build hiding (pApp)
import Language.Haskell.Exts.ExactPrint (exactPrint)
import Language.Haskell.Exts.Extension hiding (Strict, Lazy)
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Pretty
import Language.Haskell.Exts.Syntax
