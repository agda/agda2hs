module Agda2Hs.Compile.Data where

import qualified Language.Haskell.Exts.Syntax as Hs

import Control.Monad ( unless, when )
import Agda.Compiler.Backend
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Common.Pretty ( prettyShow )

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.Monad ( mapMaybeM )

import Agda2Hs.Compile.Type ( compileDomType, compileTeleBinds, compileDom, DomOutput(..) )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

checkNewtype :: Hs.Name () -> [Hs.QualConDecl ()] -> C ()
checkNewtype name cs = do
  checkSingleElement name cs "Newtype must have exactly one constructor in definition"
  case cs of
    (Hs.QualConDecl () _ _ (Hs.ConDecl () cName types):_) -> checkNewtypeCon cName types
    _ -> __IMPOSSIBLE__

compileData :: AsNewType -> [Hs.Deriving ()] -> Definition -> C [Hs.Decl ()]
compileData newtyp ds def = do
  let d = hsName $ prettyShow $ qnameName $ defName def
  checkValidTypeName d
  let Datatype{dataPars = n, dataIxs = numIxs, dataCons = cs} = theDef def
  TelV tel t <- telViewUpTo n (defType def)
  reportSDoc "agda2hs.data" 10 $ text "Datatype telescope:" <+> prettyTCM tel
  allIndicesErased t
  let params = teleArgs tel
  addContext tel $ do
    binds <- compileTeleBinds tel
    cs <- mapM (compileConstructor params) cs
    let hd = foldl (Hs.DHApp ()) (Hs.DHead () d) binds

    let target = if newtyp then Hs.NewType () else Hs.DataType ()

    when newtyp (checkNewtype d cs)

    return [Hs.DataDecl () target Nothing hd cs ds]

allIndicesErased :: Type -> C ()
allIndicesErased t = reduce (unEl t) >>= \case
  Pi dom t -> compileDomType (absName t) dom >>= \case
    DomDropped      -> allIndicesErased (unAbs t)
    DomType{}       -> genericDocError =<< text "Not supported: indexed datatypes"
    DomConstraint{} -> genericDocError =<< text "Not supported: constraints in types"
    DomForall{}     -> genericDocError =<< text "Not supported: indexed datatypes"
  _ -> return ()

compileConstructor :: [Arg Term] -> QName -> C (Hs.QualConDecl ())
compileConstructor params c = do
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
compileConstructorArgs (ExtendTel a tel) = compileDomType (absName tel) a >>= \case
  DomType s hsA     -> do
    ty <- addTyBang s hsA
    (ty :) <$> underAbstraction a tel compileConstructorArgs
  DomConstraint hsA -> genericDocError =<< text "Not supported: constructors with class constraints"
  DomDropped        -> underAbstraction a tel compileConstructorArgs
  DomForall{}       -> __IMPOSSIBLE__


checkUnboxedDataPragma :: Definition -> C ()
checkUnboxedDataPragma def = do
  let Datatype{..} = theDef def

  -- unboxed datatypes shouldn't be recursive
  unless (all null dataMutual) $ genericDocError
    =<< text "Unboxed datatype" <+> prettyTCM (defName def)
    <+> text "cannot be recursive"

  TelV tel t <- telViewUpTo dataPars (defType def)
  let params :: [Arg Term] = teleArgs tel

  allIndicesErased t

  case dataCons of
    [con] -> do
      info <- getConstInfo con
      let Constructor {..} = theDef info
      ty <- defType info `piApplyM` params
      TelV conTel _ <- telView ty
      args <- nonErasedArgs conTel
      unless (length args == 1) $ genericDocError
        =<< text "Unboxed datatype" <+> prettyTCM (defName def)
        <+> text "should have a single constructor with exactly one non-erased argument."

    _     -> genericDocError =<< text "Unboxed datatype" <+> prettyTCM (defName def)
                             <+> text "must have exactly one constructor."

  where
    nonErasedArgs :: Telescope -> C [String]
    nonErasedArgs EmptyTel = return []
    nonErasedArgs (ExtendTel a tel) = compileDom a >>= \case
      DODropped  -> underAbstraction a tel nonErasedArgs
      DOType     -> genericDocError =<< text "Type argument in unboxed datatype not supported"
      DOInstance -> genericDocError =<< text "Instance argument in unboxed datatype not supported"
      DOTerm     -> (absName tel:) <$> underAbstraction a tel nonErasedArgs

