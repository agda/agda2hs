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
import Agda.TypeChecking.Monad.Base ( genericDocError )
import Agda.TypeChecking.Monad.Context ( lookupBV )
import Agda.Utils.Monad ( whenM )


-- | Compile a variable. 
-- If the variable check is enabled, ensure that the variable is usable and visible.
compileDBVar :: Nat -> C String
compileDBVar x = do
  (d, n) <- (fmap snd &&& fst . unDom) <$> lookupBV x
  let cn = prettyShow $ nameConcrete n
  let b | notVisible d   = "hidden"
        | hasQuantity0 d = "erased"
        | otherwise      = ""
  whenM (asks checkVar) $ unless (null b) $ genericDocError =<<
    text ("Cannot use " <> b <> " variable " <> cn)
  return cn
