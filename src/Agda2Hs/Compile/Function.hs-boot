module Agda2Hs.Compile.Function where

import qualified Agda2Hs.Language.Haskell as Hs ( Match, Name )
import Agda.Syntax.Internal ( Clause, ModuleName, QName, Type )
import Agda2Hs.Compile.Types ( C )

compileClause' :: ModuleName -> Maybe QName -> Hs.Name () -> Type -> Clause -> C (Maybe (Hs.Match ()))
