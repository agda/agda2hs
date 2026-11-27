module Agda2Hs.Compile.Var where

import Agda2Hs.Compile.Types
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty ( prettyShow )
import Agda.Syntax.Abstract.Name ( nameConcrete )
import Agda.TypeChecking.Monad.Base ( ContextEntry(..) )
import Agda.TypeChecking.Monad.Context ( lookupBV )


-- | Compile a variable.
compileDBVar :: Nat -> C String
compileDBVar x = do
  n <- ceName <$> lookupBV x
  return $ prettyShow $ nameConcrete n
