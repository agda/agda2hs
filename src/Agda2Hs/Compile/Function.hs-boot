module Agda2Hs.Compile.Function where

import qualified Language.Haskell.Exts.Syntax as Hs ( Match, Name )
import Agda.Syntax.Internal ( Clause, ModuleName, Type )
import Agda2Hs.Compile.Types ( C )

compileClause' :: ModuleName -> Hs.Name () -> Type -> Clause -> C (Maybe (Hs.Match ()))
