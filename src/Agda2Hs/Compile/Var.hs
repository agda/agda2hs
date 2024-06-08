module Agda2Hs.Compile.Var where

import Control.Arrow ((&&&))
import Control.Monad (unless)
import Control.Monad.Reader.Class (asks)

import Agda.Syntax.Abstract.Name (nameConcrete)
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal (unDom)
import Agda.TypeChecking.Monad.Base (genericDocError)
import Agda.TypeChecking.Monad.Context (lookupBV)
import Agda.TypeChecking.Pretty (text)
import Agda.Utils.Monad (whenM)
import Agda2Hs.Compile.Types

-- | Compile a variable.
compileDBVar :: Nat -> C String
compileDBVar x = do
  (d, n) <- (fmap snd &&& fst . unDom) <$> lookupBV x
  return $ prettyShow $ nameConcrete n
