module Agda2Hs.Compile.Data where

import Control.Monad ( when )
import Data.List ( intercalate, partition )
import Agda.Compiler.Backend
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Common.Pretty ( prettyShow )

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.Monad ( ifNotM )

import Agda2Hs.Compile.RuntimeCheckUtils
import Agda2Hs.Compile.Type
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils


import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils ( hsName ) -- and probably some more

data DataRtcResult
  = NoRtc
  | DataNoneErased String
  | DataUncheckable
  | DataCheckable [Hs.Decl ()]

concatRtc :: [DataRtcResult] -> ([String], [Hs.Decl ()])
concatRtc [] = ([], [])
concatRtc (res : ress) = case res of
  DataNoneErased s -> (s : tlNoneErased, tlCheckable)
  DataCheckable ds -> (tlNoneErased, ds ++ tlCheckable)
  _ -> tl
  where
    tl@(tlNoneErased, tlCheckable) = concatRtc ress

checkNewtype :: Hs.Name () -> [Hs.QualConDecl ()] -> C ()
checkNewtype name cs = do
  checkSingleElement name cs "Newtype must have exactly one constructor in definition"
  case cs of
    (Hs.QualConDecl () _ _ (Hs.ConDecl () cName types):_) -> checkNewtypeCon cName types
    _ -> __IMPOSSIBLE__

compileData :: AsNewType -> [Hs.Deriving ()] -> Definition -> C RtcDecls
compileData newtyp ds def = do
  let prettyName = prettyShow $ qnameName $ defName def
      d = hsName prettyName
  checkValidTypeName d
  let Datatype{dataPars = n, dataIxs = numIxs, dataCons = cs} = theDef def
  TelV tel t <- telViewUpTo n (defType def)
  reportSDoc "agda2hs.data" 10 $ text "Datatype telescope:" <+> prettyTCM tel
  allIndicesErased t
  let params = teleArgs tel
  addContext tel $ do
    binds <- compileTeleBinds tel
    chkdCs <- mapM (compileConstructor params) cs
    chks <- ifNotM (emitsRtc $ defName def) (return []) $ do
      let (noneErased, chks) = concatRtc $ map snd chkdCs
      -- Always export data type name
      tellNoErased $ prettyName ++ "(" ++ intercalate ", " noneErased ++ ")"
      return chks

    let cs = map fst chkdCs
        hd = foldl (Hs.DHApp ()) (Hs.DHead () d) binds

    let target = if newtyp then Hs.NewType () else Hs.DataType ()

    when newtyp (checkNewtype d cs)

    return $ WithRtc [Hs.DataDecl () target Nothing hd cs ds] chks
  where
    allIndicesErased :: Type -> C ()
    allIndicesErased t = reduce (unEl t) >>= \case
      Pi dom t -> compileDomType (absName t) dom >>= \case
        DomDropped      -> allIndicesErased (unAbs t)
        DomType{}       -> agda2hsError "Not supported: indexed datatypes"
        DomConstraint{} -> agda2hsError "Not supported: constraints in types"
        DomForall{}     -> agda2hsError "Not supported: indexed datatypes"
      _ -> return ()

compileConstructor :: [Arg Term] -> QName -> C (Hs.QualConDecl (), DataRtcResult)
compileConstructor params c = do
  reportSDoc "agda2hs.data.con" 15 $ text "compileConstructor" <+> prettyTCM c
  reportSDoc "agda2hs.data.con" 20 $ text "  params = " <+> prettyTCM params
  ty <- (`piApplyM` params) . defType =<< getConstInfo c
  reportSDoc "agda2hs.data.con" 20 $ text "  ty = " <+> prettyTCM ty
  TelV tel _ <- telView ty
  let conString = prettyShow $ qnameName c
      conName = hsName conString
  smartQName <- smartConstructor c True

  checkValidConName conName
  args <- compileConstructorArgs tel
  chk <- ifNotM (emitsRtc c) (return NoRtc) $ do
    sig <- Hs.TypeSig () [hsName $ prettyShow $ qnameName smartQName] <$> compileType (unEl ty)
    -- export constructor name when none erased, provide signature for smart constructor if it exists
    checkRtc tel smartQName (Hs.hsVar conString) alternatingLevels >>= \case
      NoneErased -> return $ DataNoneErased conString
      Uncheckable -> return DataUncheckable
      Checkable ds -> return $ DataCheckable $ sig : ds

  return (Hs.QualConDecl () Nothing Nothing $ Hs.ConDecl () conName args, chk)

compileConstructorArgs :: Telescope -> C [Hs.Type ()]
compileConstructorArgs EmptyTel = return []
compileConstructorArgs (ExtendTel a tel) = compileDomType (absName tel) a >>= \case
  DomType s hsA     -> do
    ty <- addTyBang s hsA
    (ty :) <$> underAbstraction a tel compileConstructorArgs
  DomConstraint hsA -> agda2hsError "Not supported: constructors with class constraints"
  DomDropped        -> underAbstraction a tel compileConstructorArgs
  DomForall{}       -> __IMPOSSIBLE__
