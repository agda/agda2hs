module Agda2Hs.Compile.TypeDefinition where

import Control.Arrow ( (>>>), (***), (&&&), first, second )
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader

import Data.Generics ( mkT, everywhere, listify, extT, everything, mkQ, Data )
import Data.List
import Data.List.NonEmpty ( NonEmpty(..) )
import Data.Maybe
import Data.Map ( Map )
import qualified Data.Text as Text
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap

import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Build as Hs
import qualified Language.Haskell.Exts.Parser as Hs
import qualified Language.Haskell.Exts.Extension as Hs

import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.BasicOps

import Agda.Syntax.Common hiding ( Ranged )
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad hiding ( withCurrentModule )

import Agda.TypeChecking.CheckInternal ( infer )
import Agda.TypeChecking.Constraints ( noConstraints )
import Agda.TypeChecking.Conversion ( equalTerm )
import Agda.TypeChecking.InstanceArguments ( findInstance )
import Agda.TypeChecking.Level ( isLevelType )
import Agda.TypeChecking.MetaVars ( newInstanceMeta )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce ( instantiate, reduce )
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Records
import Agda.TypeChecking.Sort ( ifIsSort )

import Agda.Utils.Lens
import Agda.Utils.Pretty ( prettyShow )
import qualified Agda.Utils.Pretty as P
import Agda.Utils.List
import Agda.Utils.Impossible
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Functor

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name
import Agda2Hs.Compile.Type
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils
import Agda2Hs.Pragma

compileTypeDef :: Hs.Name () -> Definition -> LocalDecls -> C [Hs.Decl ()]
compileTypeDef name (Defn {..}) locals = do
  noLocals locals
  Clause{..} <- singleClause funClauses
  addContext (KeepNames clauseTel) $ liftTCM1 localScope $ do
    as <- compileTypeArgs namedClausePats
    let hd = foldl (Hs.DHApp ()) (Hs.DHead () name) as
    rhs <- compileType $ fromMaybe __IMPOSSIBLE__ clauseBody
    return [Hs.TypeDecl () hd rhs]

  where
    Function{..} = theDef
    noLocals locals = unless (null locals) $
      genericError "Not supported: type definition with `where` clauses"
    singleClause = \case
      [cl] -> return cl
      _    -> genericError "Not supported: type definition with several clauses"

compileTypeArgs :: NAPs -> C [Hs.TyVarBind ()]
compileTypeArgs ps = mapM (compileTypeArg . namedArg) $ filter keepArg ps

compileTypeArg :: DeBruijnPattern -> C (Hs.TyVarBind ())
compileTypeArg p@(VarP o _) = Hs.UnkindedVar () . hsName <$> showTCM p
compileTypeArg _ = genericError "Not supported: type definition by pattern matching"
