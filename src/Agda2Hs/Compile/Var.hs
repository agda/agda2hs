module Agda2Hs.Compile.Var where

import Control.Arrow ( (&&&) )
import Control.Monad ( unless )
import Control.Monad.Reader.Class ( asks )

import Agda2Hs.Compile.Types
import Agda.Syntax.Common
import Agda.Syntax.Internal ( unDom )
import Agda.Syntax.Common.Pretty ( prettyShow )
import Agda.Syntax.Abstract.Name ( nameConcrete )
import Agda.TypeChecking.Pretty ( text )
import Agda.TypeChecking.Monad.Base ( ContextEntry(..) )
import Agda.TypeChecking.Monad.Context ( lookupBV )
import Agda.Utils.Monad ( whenM )


-- | Compile a variable.
compileDBVar :: Nat -> C String
compileDBVar x = do
  n <- ceName <$> lookupBV x
  return $ prettyShow $ nameConcrete n
