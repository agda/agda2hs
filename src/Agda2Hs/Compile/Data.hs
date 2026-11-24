module Agda2Hs.Compile.Data where

import Agda.Compiler.Backend
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings ( warning )

import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Singleton
import Agda.Utils.Impossible ( __IMPOSSIBLE__ )

import Agda2Hs.AgdaUtils

import Agda2Hs.Compile.Exports ( tellDefinitionExport )
import Agda2Hs.Compile.Name
import Agda2Hs.Compile.Type ( compileType, compileDomType, compileTeleBinds, compileDom )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils

import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils ( alphaEq )

import Agda2Hs.Pragma

checkNewtype :: Hs.Name () -> [Hs.QualConDecl ()] -> C ()
checkNewtype name cs = do
  checkSingleElement name cs "Newtype must have exactly one constructor in definition"
  case cs of
    (Hs.QualConDecl () _ _ (Hs.ConDecl () cName types):_) -> checkNewtypeCon cName types
    _ -> __IMPOSSIBLE__

compileData :: DataTarget -> [Hs.Deriving ()] -> Definition -> C [Hs.Decl ()]
compileData target ds def = do
  let d = compileName (qnameName $ defName def)
  checkValidTypeName d
  tellTypeOperators d

  tellDefinitionExport def

  let Datatype{dataPars = n, dataIxs = numIxs, dataCons = cs} = theDef def
  TelV tel t <- telViewUpTo n (defType def)
  reportSDoc "agda2hs.data" 10 $ text "Datatype telescope:" <+> prettyTCM tel
  allIndicesErased t
  let params = teleArgs tel
  binds <- compileTeleBinds False tel -- TODO: add kind annotations?
  addContext tel $ do
    let hd = foldl (Hs.DHApp ()) (Hs.DHead () d) binds
    let htarget = toDataTarget target
    -- TODO: filter out erased constructors
    case target of
      ToGadt -> do
        tellExtension Hs.GADTs
        cs <- mapM (compileGadtConstructor params) cs
        return $ singleton $ Hs.GDataDecl () htarget Nothing hd Nothing cs ds
      _ -> do
        cs <- mapM (compileConstructor params) cs
        when (target == ToNewType) (checkNewtype d cs)
        return $ singleton $ Hs.DataDecl () htarget Nothing hd cs ds

allIndicesErased :: Type -> C ()
allIndicesErased t = reduce (unEl t) >>= \case
  Pi dom t -> compileDomType (absName t) dom >>= \case
    DomDropped      -> allIndicesErased (unAbs t)
    DomType{}       -> agda2hsError "Not supported: indexed datatypes"
    DomConstraint{} -> agda2hsError "Not supported: constraints in types"
    DomForall{}     -> agda2hsError "Not supported: indexed datatypes"
  _ -> return ()

-- | The information about a constructor that is shared between the different
--   compilation targets. The result type is only needed for GADT syntax and for
--   checking a @compile-to@ pragma, so it is only computed on demand.
data CompiledConstructor = CompiledConstructor
  { constructorName   :: Hs.Name ()
  , constructorArgs   :: [Hs.Type ()]
  , constructorResult :: Maybe (Hs.Type ())
  }

-- | Compile a constructor to a regular Haskell constructor declaration.
compileConstructor :: [Arg Term] -> QName -> C (Hs.QualConDecl ())
compileConstructor params c = do
  info <- compileConstructorInfo False params c
  return $ Hs.QualConDecl () Nothing Nothing $
    Hs.ConDecl () (constructorName info) (constructorArgs info)

-- | Compile a constructor to a Haskell GADT constructor declaration.
compileGadtConstructor :: [Arg Term] -> QName -> C (Hs.GadtDecl ())
compileGadtConstructor params c = do
  info <- compileConstructorInfo True params c
  case constructorResult info of
    Nothing  -> __IMPOSSIBLE__
    Just ret -> return $ Hs.GadtDecl () (constructorName info) Nothing Nothing Nothing $
      foldr (Hs.TyFun ()) ret (constructorArgs info)

-- | Compute the information about a constructor that is shared between the
--   different compilation targets.
compileConstructorInfo :: Bool -> [Arg Term] -> QName -> C CompiledConstructor
compileConstructorInfo withResult params c = do
  reportSDoc "agda2hs.data.con" 15 $ text "compileConstructor" <+> prettyTCM c
  reportSDoc "agda2hs.data.con" 20 $ text "  params = " <+> prettyTCM params
  ty <- defType <$> getConstInfo c
  reportSDoc "agda2hs.data.con" 30 $ text "  ty (before piApply) = " <+> prettyTCM ty
  ty <- ty `piApplyM` params
  reportSDoc "agda2hs.data.con" 20 $ text "  ty = " <+> prettyTCM ty
  TelV tel ret <- telView ty
  let conName = compileName (qnameName c)
  checkValidConName conName
  args <- compileConstructorArgs tel
  hret <- if withResult then Just <$> (addContext tel $ compileType $ unEl ret) else return Nothing
  return $ CompiledConstructor conName args hret

compileConstructorArgs :: Telescope -> C [Hs.Type ()]
compileConstructorArgs EmptyTel = return []
compileConstructorArgs (ExtendTel a tel) = compileDomType (absName tel) a >>= \case
  DomType s hsA      -> do
    ty <- addTyBang s hsA
    (ty :) <$> underAbstraction a tel compileConstructorArgs
  DomConstraint hsA  -> agda2hsError "Not supported: constructors with class constraints"
  DomDropped         -> skip
  DomForall Nothing  -> skip
  DomForall (Just _) -> __IMPOSSIBLE__
  where skip = underAbstraction a tel compileConstructorArgs

checkCompileToDataPragma :: Definition -> String -> C ()
checkCompileToDataPragma def s = noCheckNames $ noWriteExports $ do
  r <- resolveStringName s
  let ppd = prettyTCM (defName def)
      ppr = prettyTCM r
  let fail reason = agda2hsErrorM $
        "Cannot compile datatype" <+> liftTCM ppd <+>
        "to" <+> liftTCM ppr <+> "because" <+> reason
      -- The constructors of a compile-to datatype are not generated, so a
      -- mismatch in their names only means that the generated code uses
      -- different names than the Agda source, not that it fails to compile.
      -- Emit a warning instead of an error in that case.
      warn reason = warning =<< (CustomBackendWarning "agda2hs" <$> vcat
        [ "The datatype" <+> liftTCM ppd <+> "is annotated with a `to` pragma"
            <+> "targeting" <+> (liftTCM ppr <> text ",")
        , nest 2 $ "but" <+> reason ])
  -- Start by adding compile-to rule because it makes the check
  -- for constructor types easier
  addCompileToName (defName def) r
  -- Check that target is a datatype with a regular COMPILE pragma
  reportSDoc "agda2hs.compileto" 20 $ "Checking that" <+> ppr <+> "is a datatype"
  unlessM (liftTCM $ isDatatype r) $ fail "it is not a datatype"
  (rdef, rpragma) <- getDefAndPragma r
  whenNothing (isSpecialCon r) $ case rpragma of
    DefaultPragma{} -> return ()
    NewTypePragma{} -> return ()
    GadtPragma{} -> return ()
    NoPragma{} -> do
      -- A datatype from a primitive module (such as `Bool`) is bound to an
      -- existing Haskell type without a COMPILE pragma.
      (mkind, _, _) <- compileModuleName (qnameModule r)
      unless (mkind == PrimModule) $ fail "it is missing a COMPILE pragma"
    _ -> fail "it has an unsupported COMPILE pragma"
  -- Check that parameters match
  reportSDoc "agda2hs.compileto" 20 $ "Checking that parameters of" <+> ppd <+> "match those of" <+> ppr
  TelV dtel dtarget <- telViewUpTo (dataPars $ theDef def) (defType def)
  rtel <- theTel <$> telViewUpTo (dataPars $ theDef rdef) (defType rdef)
  dpars <- compileTeleBinds True dtel
  rpars <- compileTeleBinds True rtel
  unless (length rpars == length dpars) $ fail
    "they have a different number of parameters"
  forM_ (zip dpars rpars) $ \(Hs.KindedVar _ a ak, Hs.KindedVar _ b bk) ->
    unless (alphaEq ak bk) $ fail $
      "parameter" <+> text (Hs.pp a) <+> "of kind" <+> text (Hs.pp ak) <+>
      "does not match" <+> text (Hs.pp b) <+> "of kind" <+> text (Hs.pp bk)
  -- Check that d has no non-erased indices
  addContext dtel $ allIndicesErased dtarget
  -- Check that constructors match
  -- TODO: filter out erased constructors
  reportSDoc "agda2hs.compileto" 20 $ "Checking that constructors of" <+> ppd <+> "match those of" <+> ppr
  let dcons = dataCons $ theDef def
      rcons = dataCons $ theDef rdef
  unless (length rcons == length dcons) $ fail
    "they have a different number of constructors"
  forM_ (zip dcons rcons) $ \(c1, c2) -> do
    CompiledConstructor hsC1 args1 (Just rt1) <-
      addContext dtel $ compileConstructorInfo True (teleArgs dtel) c1
    -- rename parameters of r to match those of d
    rtel' <- renameParameters dtel rtel
    CompiledConstructor hsC2 args2 (Just rt2) <-
      addContext rtel' $ compileConstructorInfo True (teleArgs rtel') c2
    -- The result types should be equal. On the current feature set this is
    -- automatic, because the datatype is not allowed to have any non-erased
    -- indices and the parameters have already been checked to match. The check
    -- matters once indexed (GADT) datatypes are supported.
    unless (alphaEq rt1 rt2) $ fail $
      "the result type of constructor" <+> text (Hs.pp hsC1) <+>
      "does not match" <+> text (Hs.pp hsC2)
    unless (hsC1 == hsC2) $ warn $
      "the name of constructor" <+> text (Hs.pp hsC1) <+>
      "does not match" <+> text (Hs.pp hsC2)
    unless (length args1 == length args2) $ fail $
      "number of arguments to" <+> text (Hs.pp hsC1) <+>
      "does not match with" <+> text (Hs.pp hsC2)
    forM_ (zip args1 args2) $ \(b1, b2) ->
      unless (alphaEq b1 b2) $ fail $
        "constructor argument type" <+> text (Hs.pp b1) <+>
        "does not match with" <+> text (Hs.pp b2)
    addCompileToName c1 c2

  where
    -- Use the names of the non-erased variables in the first telescope
    -- as the names of the non-erased variables in the second telescope.
    renameParameters :: Telescope -> Telescope -> C Telescope
    renameParameters tel1 tel2 = flip loop tel2 =<< nonErasedNames tel1
      where
        loop :: [ArgName] -> Telescope -> C Telescope
        loop _ EmptyTel = pure EmptyTel
        loop [] tel = pure tel
        loop (x:xs) (ExtendTel dom tel) = compileDom dom >>= \case
          DOType -> ExtendTel dom . Abs x <$>
            underAbstraction dom tel (loop xs)
          DODropped -> ExtendTel dom . Abs (absName tel) <$>
            underAbstraction dom tel (loop (x:xs))
          DOTerm -> __IMPOSSIBLE__
          DOInstance -> __IMPOSSIBLE__

    nonErasedNames :: Telescope -> C [ArgName]
    nonErasedNames EmptyTel = pure []
    nonErasedNames (ExtendTel dom tel) = do
      cd <- compileDom dom
      let mx = case cd of
            DOType -> (absName tel :)
            DODropped -> id
            DOTerm -> __IMPOSSIBLE__
            DOInstance -> __IMPOSSIBLE__
      mx <$> underAbstraction dom tel nonErasedNames

