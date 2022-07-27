module Agda2Hs.Compile.Function where

import qualified Language.Haskell.Exts.Syntax as Hs
import Agda.Syntax.Internal
import Agda2Hs.Compile.Types

compileClause :: LocalDecls -> Hs.Name () -> Clause -> C (LocalDecls, Hs.Match ())
