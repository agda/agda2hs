module Agda2Hs.Compile.TypeDefinition where

import Control.Monad ( unless )

import Data.Maybe ( fromMaybe )

import qualified Language.Haskell.Exts.Syntax as Hs

import Agda.Compiler.Backend

import Agda.Syntax.Common ( namedArg )
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Telescope ( mustBePi )

import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.Monad

import Agda2Hs.Compile.Type ( compileType, compileDom, DomOutput(..), compileTypeArgs )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.Compile.Var ( compileDBVar )
import Agda2Hs.Language.Haskell.Utils
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.TypeChecking.Substitute


compileTypeDef :: Hs.Name () -> Definition -> C [Hs.Decl ()]
compileTypeDef name (Defn {..}) = do
  unlessM (isTransparentFunction defName) $ checkValidTypeName name
  Clause{..} <- singleClause funClauses
  addContext (KeepNames clauseTel) $ do
    as <- compileTypePatternArgs defType namedClausePats
    let hd = foldl (Hs.DHApp ()) (Hs.DHead () name) as
    rhs <- compileType $ fromMaybe __IMPOSSIBLE__ clauseBody
    return [Hs.TypeDecl () hd rhs]
  where
    Function{..} = theDef
    singleClause = \case
      [cl] -> return cl
      _    -> genericError "Not supported: type definition with several clauses"

compileTypePatternArgs :: Type -> NAPs -> C [Hs.TyVarBind ()]
compileTypePatternArgs ty naps = do
  aux <- compileTypeArgs ty $ fromMaybe __IMPOSSIBLE__ $ allApplyElims $ patternsToElims naps
  mapM assertIsTyVarBind aux
  where
    assertIsTyVarBind :: Hs.Type () -> C (Hs.TyVarBind ())
    assertIsTyVarBind = \case
      Hs.TyVar _ n -> pure $ Hs.UnkindedVar () n
      _ -> genericError "Not supported: type definition by pattern matching"

compileTypeArg :: DeBruijnPattern -> C (Hs.TyVarBind ())
compileTypeArg p@(VarP o i) = do
  name <- hsName <$> compileDBVar (dbPatVarIndex i)
  checkValidTyVarName name
  return $ Hs.UnkindedVar () name
compileTypeArg _ = genericError "Not supported: type definition by pattern matching"
