module Agda2Hs.Compile.Data where

import qualified Language.Haskell.Exts.Syntax as Hs

import Agda.Compiler.Backend
import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Pretty ( prettyShow )
import Agda.Utils.Impossible ( __IMPOSSIBLE__ )

import Agda2Hs.Compile.Type ( compileDom, compileTele )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

compileData :: [Hs.Deriving ()] -> Definition -> C [Hs.Decl ()]
compileData ds def = do
  let d = hsName $ prettyShow $ qnameName $ defName def
  case theDef def of
    Datatype{dataPars = n, dataIxs = numIxs, dataCons = cs} -> do
      TelV tel t <- telViewUpTo n (defType def)
      reportSDoc "agda2hs.data" 10 $ text "Datatype telescope:" <+> prettyTCM tel
      allIndicesErased t
      params <- compileTele tel
      addContext tel $ do
        pars <- mapM (showTCM . unArg) params
        cs   <- mapM (compileConstructor params) cs
        let hd   = foldl (\ h p -> Hs.DHApp () h (Hs.UnkindedVar () $ hsName p))
                         (Hs.DHead () d) pars
        return [Hs.DataDecl () (Hs.DataType ()) Nothing hd cs ds]
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
compileConstructor params c = do
  ty <- (`piApplyM` params) . defType =<< getConstInfo c
  TelV tel _ <- telView ty
  let conName = hsName $ prettyShow $ qnameName c
  args <- compileConstructorArgs tel
  return $ Hs.QualConDecl () Nothing Nothing $ Hs.ConDecl () conName args

compileConstructorArgs :: Telescope -> C [Hs.Type ()]
compileConstructorArgs EmptyTel = return []
compileConstructorArgs (ExtendTel a tel) = compileDom (absName tel) a >>= \case
  DomType hsA       -> (hsA :) <$> underAbstraction a tel compileConstructorArgs
  DomConstraint hsA -> genericDocError =<< text "Not supported: constructors with class constraints"
  DomDropped        -> underAbstraction a tel compileConstructorArgs
