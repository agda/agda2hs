module Agda2Hs.Compile.Function where

import qualified Language.Haskell.Exts.Syntax as Hs ( Match, Name )
import Agda.Syntax.Internal ( Clause )
import Agda2Hs.Compile.Types ( C, LocalDecls )

compileClause :: LocalDecls -> Hs.Name () -> Clause -> C (LocalDecls, Hs.Match ())
