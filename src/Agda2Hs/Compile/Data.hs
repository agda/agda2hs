module Agda2Hs.Compile.Data where

import qualified Language.Haskell.Exts.Syntax as Hs

import Agda.Compiler.Backend
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Common.Pretty ( prettyShow )

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Impossible ( __IMPOSSIBLE__ )

import Agda2Hs.Compile.Type ( compileDom, compileTeleBinds )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

checkNewtype :: Hs.Name () -> [Hs.QualConDecl ()] -> C ()
checkNewtype name cs = do
  checkSingleElement name cs "Newtype must have exactly one constructor in definition"
  case head cs of
    Hs.QualConDecl () _ _ (Hs.ConDecl () cName types)
      -> checkSingleElement cName types "Newtype must have exactly one field in constructor"

compileData :: DataTarget -> [Hs.Deriving ()] -> Definition -> C [Hs.Decl ()]
compileData target ds def = do
  let d = hsName $ prettyShow $ qnameName $ defName def
  checkValidTypeName d
  case theDef def of
    Datatype{dataPars = n, dataIxs = numIxs, dataCons = cs} -> do
      TelV tel t <- telViewUpTo n (defType def)
      reportSDoc "agda2hs.data" 10 $ text "Datatype telescope:" <+> prettyTCM tel
      allIndicesErased t
      let params = teleArgs tel
      addContext tel $ do
        binds <- compileTeleBinds tel
        cs <- mapM (compileConstructor params) cs
        let hd = foldl (Hs.DHApp ()) (Hs.DHead () d) binds

        case target of
          ToData -> return [Hs.DataDecl () (Hs.DataType ()) Nothing hd cs ds]
          ToDataNewType -> do
            checkNewtype d cs
            return [Hs.DataDecl () (Hs.NewType ()) Nothing hd cs ds]
    _ -> __IMPOSSIBLE__
  where
    allIndicesErased :: Type -> C ()
    allIndicesErased t = reduce (unEl t) >>= \case
      Pi dom t -> compileDom (absName t) dom >>= \case
        DomDropped      -> allIndicesErased (unAbs t)
        DomType{}       -> genericDocError =<< text "Not supported: indexed datatypes"
        DomConstraint{} -> genericDocError =<< text "Not supported: constraints in types"
      _ -> return ()

compileConstructor :: [Arg Term] -> QName -> C (Hs.QualConDecl ())
compileConstructor params c = checkingVars $ do
  reportSDoc "agda2hs.data.con" 15 $ text "compileConstructor" <+> prettyTCM c
  reportSDoc "agda2hs.data.con" 20 $ text "  params = " <+> prettyTCM params
  ty <- (`piApplyM` params) . defType =<< getConstInfo c
  reportSDoc "agda2hs.data.con" 20 $ text "  ty = " <+> prettyTCM ty
  TelV tel _ <- telView ty
  let conName = hsName $ prettyShow $ qnameName c
  checkValidConName conName
  args <- compileConstructorArgs tel
  return $ Hs.QualConDecl () Nothing Nothing $ Hs.ConDecl () conName args

compileConstructorArgs :: Telescope -> C [Hs.Type ()]
compileConstructorArgs EmptyTel = return []
compileConstructorArgs (ExtendTel a tel) = compileDom (absName tel) a >>= \case
  DomType s hsA     -> do
    ty <- addTyBang s hsA
    (ty :) <$> underAbstraction a tel compileConstructorArgs
  DomConstraint hsA -> genericDocError =<< text "Not supported: constructors with class constraints"
  DomDropped        -> underAbstraction a tel compileConstructorArgs
