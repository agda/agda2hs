module Agda2Hs.Compile.Function where

import Control.Arrow ( (***) )
import Control.Monad ( (>=>), filterM, forM_ )
import Control.Monad.Reader ( asks, local )

import Data.Generics
import Data.List
import Data.Maybe ( fromMaybe, isJust )
import qualified Data.Text as Text

import Agda.Compiler.Backend
import Agda.Compiler.Common

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern ( patternToTerm )
import Agda.Syntax.Literal
import Agda.Syntax.Common.Pretty ( prettyShow )
import Agda.Syntax.Scope.Monad ( isDatatypeModule )

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Sort ( ifIsSort )
import Agda.TypeChecking.Datatypes ( getConType, isDataOrRecord )
import Agda.TypeChecking.Records ( getDefType )
import Agda.TypeChecking.Reduce ( reduce )

import Agda.Utils.Functor ( (<&>), dget)
import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.Lens ((^.))
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Size ( Sized(size) )

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name ( compileQName )
import Agda2Hs.Compile.RuntimeCheckUtils
import Agda2Hs.Compile.Term ( compileTerm, usableDom )
import Agda2Hs.Compile.Type ( compileType, compileDom, DomOutput(..), compileDomType )
import Agda2Hs.Compile.TypeDefinition ( compileTypeDef )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.Compile.Var ( compileDBVar )

import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils
  ( Strictness, hsName, pApp, patToExp, constrainType, qualifyType )

-- | Compilation rules for specific constructors in patterns.
isSpecialCon :: QName -> Maybe (Type -> NAPs -> C (Hs.Pat ()))
isSpecialCon qn = case prettyShow qn of
  s | s `elem` badConstructors     -> Just itsBad
  "Agda.Builtin.Int.Int.pos"       -> Just posIntPat
  "Agda.Builtin.Int.Int.negsuc"    -> Just negSucIntPat
  _                                -> Nothing
  where
    badConstructors =
      [ "Agda.Builtin.Nat.Nat.zero"
      , "Agda.Builtin.Nat.Nat.suc"
      , "Haskell.Extra.Delay.Delay.now"
      , "Haskell.Extra.Delay.Delay.later"
      ]

    itsBad :: Type -> NAPs -> C (Hs.Pat ())
    itsBad _ _ = agda2hsErrorM $ "constructor `" <> prettyTCM qn <> "` not supported in patterns"

-- | Translate Int.pos pattern.
posIntPat :: Type -> NAPs -> C (Hs.Pat ())
posIntPat ty [p] = do
  n <- compileLitNatPat (namedArg p)
  return $ Hs.PLit () (Hs.Signless ()) (Hs.Int () n (show n))
posIntPat _ _ = __IMPOSSIBLE__


-- | Translate Int.negsuc pattern.
negSucIntPat :: Type -> NAPs -> C (Hs.Pat ())
negSucIntPat ty [p] = do
  n <- (1+) <$> compileLitNatPat (namedArg p)
  return $ Hs.PLit () (Hs.Negative ()) (Hs.Int () n (show (negate n)))
negSucIntPat _ _ = __IMPOSSIBLE__

-- Agda2Hs does not support natural number patterns directly (since
-- they don't exist in Haskell), however they occur as part of
-- patterns of type Integer, so we need to compile literal natural
-- number patterns.
compileLitNatPat :: DeBruijnPattern -> C Integer
compileLitNatPat = \case
  ConP ch _ ps
    | prettyShow (conName ch) == "Agda.Builtin.Nat.Nat.zero" -> return 0
    | prettyShow (conName ch) == "Agda.Builtin.Nat.Nat.suc"
    , [p] <- ps -> (1+) <$> compileLitNatPat (namedArg p)
  p -> agda2hsErrorM $ "not a literal natural number pattern:" <?> prettyTCM p


compileFun, compileFun'
  :: Bool -- ^ Whether the type signature shuuld also be generated
  -> Definition -> C RtcDecls

compileFun withSig def@Defn{..} =
  setCurrentRangeQ defName
    $ maybePrependFixity defName (defName ^. lensFixity)
    -- initialize locals when first stepping into a function
    $ withFunctionLocals defName
    $ compileFun' withSig def

-- inherit existing (instantiated) locals
compileFun' withSig def@Defn{..} = inTopContext $ withCurrentModule m $ do
  reportSDoc "agda2hs.compile" 6 $ "Compiling function: " <+> prettyTCM defName

  whenM ((withSig &&) <$> inRecordMod defName) $
    agda2hsError "not supported: functions inside a record module"

  ifM (endsInSort defType)
    -- if the function type ends in Sort, it's a type alias!
    ((`WithRtc` []) <$> (ensureNoLocals err >> compileTypeDef x def))
    -- otherwise, we have to compile clauses.
    $ do
    tel <- lookupSection m

    -- If this is a top-level function, we compile the module parameters so
    -- we can add them to the type signature and patterns.
    (paramTy , paramPats) <- ifM (asks compilingLocal) (return (id, [])) $ compileModuleParams tel

    addContext tel $ do

      -- Jesper: we need to set the checkpoint for the current module so that
      -- the canonicity check for typeclass instances picks up the
      -- module parameters (see https://github.com/agda/agda2hs/issues/305).
      liftTCM $ setModuleCheckpoint m

      -- We apply the function clause to the module parameters from the context.
      -- In case of a projection-like function, the clause is already
      -- (partially or fully) applied so we should not apply again
      -- (see https://github.com/agda/agda2hs/issues/359)
      let droppedPars = case funProjection of
            Left{} -> 0
            Right proj -> size $ getProjLams $ projLams proj
      pars <- drop droppedPars <$> getContextArgs
      reportSDoc "agda2hs.compile.type" 8 $ "Function module parameters: " <+> prettyTCM pars

      reportSDoc "agda2hs.compile.type" 8 $ "Function type (before instantiation): " <+> inTopContext (prettyTCM defType)
      typ <- piApplyM defType pars
      reportSDoc "agda2hs.compile.type" 8 $ "Function type (after instantiation): " <+> prettyTCM typ

      sig <- if not withSig then return [] else do
        checkValidFunName x
        ty <- paramTy <$> compileType (unEl typ)
        reportSDoc "agda2hs.compile.type" 8 $ "Compiled function type: " <+> text (Hs.prettyPrint ty)
        return [Hs.TypeSig () [x] ty]

      let clauses = funClauses `apply` pars
      cs  <- map (addPats paramPats) <$>
        mapMaybeM (compileClause m (Just defName) x typ) clauses

      when (null cs) $ agda2hsErrorM $
            text "Functions defined with absurd patterns exclusively are not supported."
        <+> text "Use function `error` from the Haskell.Prelude instead."

      let def = sig ++ [Hs.FunBind () cs]
      chk <- ifNotM (emitsRtc defName) (return []) $ do
        let typeTel = theTel $ telView' defType
            success = Hs.hsVar $ prettyShow m ++ ".PostRtc." ++ prettyShow n
        checkRtc typeTel defName success alternatingLevels >>= \case
          NoneErased -> do tellNoErased $ prettyShow n; return []
          Uncheckable -> return []
          Checkable ds -> return $ sig ++ ds
      return $ WithRtc def chk
  where
    Function{..} = theDef
    m = qnameModule defName
    n = qnameName defName
    x = hsName $ prettyShow n
    err = "Not supported: type definition with `where` clauses"

    addPats :: [Hs.Pat ()] -> Hs.Match () -> Hs.Match ()
    addPats [] cl = cl
    addPats ps (Hs.Match l f qs rhs bs) = Hs.Match l f (ps++qs) rhs bs
    addPats (p:ps) (Hs.InfixMatch l q f qs rhs bs) = Hs.InfixMatch l p f (ps++q:qs) rhs bs

compileModuleParams :: Telescope -> C (Hs.Type () -> Hs.Type () , [Hs.Pat ()])
compileModuleParams EmptyTel = return (id, [])
compileModuleParams (ExtendTel a tel) = do
  (f , p) <- compileDomType (absName tel) a >>= \case
    DomDropped -> return (id, [])
    DomConstraint c -> return (constrainType c, [])
    DomForall a -> return (qualifyType a, [])
    DomType s a -> do
      let n = hsName $ absName tel
      checkValidVarName n
      return (Hs.TyFun () a, [Hs.PVar () n])
  ((f .) *** (p++)) <$> underAbstraction a tel compileModuleParams

compileClause :: ModuleName -> Maybe QName -> Hs.Name () -> Type -> Clause -> C (Maybe (Hs.Match ()))
compileClause curModule mproj x t c =
  withClauseLocals curModule c $ do
    compileClause' curModule mproj x t c

compileClause' :: ModuleName -> Maybe QName -> Hs.Name () -> Type -> Clause -> C (Maybe (Hs.Match ()))
compileClause' curModule projName x ty c@Clause{..} = do
  reportSDoc "agda2hs.compile" 7  $ "compiling clause: " <+> prettyTCM c

  ifNotM (keepClause c) (pure Nothing) $ addContext (KeepNames clauseTel) $ do
    reportSDoc "agda2hs.compile" 17 $ "Old context: "      <+> (inTopContext . prettyTCM =<< getContext)
    reportSDoc "agda2hs.compile" 17 $ "Clause telescope: " <+> inTopContext (prettyTCM clauseTel)
    reportSDoc "agda2hs.compile" 17 $ "Clause type:      " <+> prettyTCM clauseType
    reportSDoc "agda2hs.compile" 17 $ "Function type:    " <+> prettyTCM ty
    reportSDoc "agda2hs.compile" 17 $ "Clause patterns:  " <+> text (prettyShow namedClausePats)
    reportSDoc "agda2hs.compile" 18 $ "Clause module:" <+> prettyTCM curModule
    ls <- asks locals
    reportSDoc "agda2hs.compile" 18 $ "Clause locals:" <+> prettyTCM ls

    toDrop <- case projName of
      Nothing -> pure 0
      Just q  -> maybe 0 (pred . projIndex) <$> isProjection q

    reportSDoc "agda2hs.compile" 17 $ "Args to drop (proj-like): " <+> prettyTCM toDrop

    -- NOTE(flupe: for projection-like definitions, we drop the first parameters)
    let ntel = size clauseTel
    ty <- ty `piApplyM` [Var (ntel - k - 1) [] | k <- [0.. (toDrop - 1)]]

    reportSDoc "agda2hs.compile" 17 $ "Corrected type: " <+> prettyTCM ty

    ps <- compilePats ty namedClausePats

    let isWhereDecl = not . isExtendedLambdaName
          /\ (curModule `isFatherModuleOf`) . qnameModule

    children   <- filter isWhereDecl <$> asks locals
    -- TODO: remove this when Agda exposes where-provenance in 'Internal' syntax
    let withWhereModule = case children of
          []    -> id
          (c:_) -> addWhereModule $ qnameModule c
    whereDecls <- withWhereModule $ compileLocal $ mapM (getConstInfo >=> compileFun' True) children

    let Just body            = clauseBody
        Just (unArg -> typ)  = clauseType

    hsBody <- withWhereModule $ compileTerm typ body

    let rhs = Hs.UnGuardedRhs () hsBody
        whereBinds | null whereDecls = Nothing
                   | otherwise       = Just $ Hs.BDecls () (concatMap defn whereDecls)
        match = case (x, ps) of
          (Hs.Symbol{}, p : q : ps) -> Hs.InfixMatch () p x (q : ps) rhs whereBinds
          _                         -> Hs.Match () x ps rhs whereBinds
    return $ Just match

keepClause :: Clause -> C Bool
keepClause c@Clause{..} = case (clauseBody, clauseType) of
  (Nothing, _) -> pure False
  (_, Nothing) -> pure False
  (Just body, Just cty) -> compileDom (domFromArg cty) <&> \case
    DODropped  -> False
    DOInstance -> True
    DOType     -> __IMPOSSIBLE__
    DOTerm     -> True


-- TODO(flupe): projection-like definitions are missing the first (variable) patterns
--             (that are however present in the type)
--             so we should drop the first parameters in the input type (using funProjection.projLams)
compilePats :: Type -> NAPs -> C [Hs.Pat ()]
compilePats _ [] = pure []
compilePats ty ((namedArg -> ProjP po pn):ps) = do
  reportSDoc "agda2hs.compile" 10 $ "compiling copattern: " <+> text (prettyShow pn)
  unlessM (asks copatternsEnabled `or2M` (isJust <$> isUnboxProjection pn)) $
    agda2hsError "not supported in Haskell: copatterns"

  ty     <- fromMaybe __IMPOSSIBLE__ <$> getDefType pn ty
  (a, b) <- mustBePi ty

  compilePats (absBody b) ps

compilePats ty ((namedArg -> pat):ps) = do
  (a, b) <- mustBePi ty
  reportSDoc "agda2hs.compile.pattern" 10 $ text "Compiling pattern:" <+> prettyTCM pat
  let rest = compilePats (absApp b (patternToTerm pat)) ps
  when (usableDom a) checkForced
  compileDom a >>= \case
    DOInstance -> rest
    DODropped  -> rest
    DOType     -> rest
    DOTerm     -> do
      checkNoAsPatterns pat
      (:) <$> compilePat (unDom a) pat <*> rest
  where checkForced  = when (isForcedPat pat) $ agda2hsError "not supported: forced (dot) patterns in non-erased positions"


compilePat :: Type -> DeBruijnPattern -> C (Hs.Pat ())

-- variable pattern
compilePat ty p@(VarP o x)
  | PatOWild <- patOrigin o = return $ Hs.PWildCard ()
  | otherwise = do
      n <- hsName <$> compileDBVar (dbPatVarIndex x)
      checkValidVarName n
      return $ Hs.PVar () n

-- special constructor pattern
compilePat ty (ConP ch i ps) = do
  Just ((_, _, _), ty) <- getConType ch =<< reduce ty
  let c = conName ch

  ifJust (isSpecialCon c) (\semantics -> setCurrentRange ch $ semantics ty ps) $ do
  ifJustM (isUnboxConstructor c) (\s -> compileErasedConP ty s ps) $ do
  ifJustM (isTupleConstructor c) (\b -> compileTupleConP ty b ps) $ do
    ps <- compilePats ty ps
    c <- compileQName (conName ch)
    return $ pApp c ps

-- literal patterns
compilePat ty (LitP _ l) = compileLitPat l


-- nothing else is supported
compilePat _ p = agda2hsErrorM $ "bad pattern:" <?> prettyTCM p


compileErasedConP :: Type -> Strictness -> NAPs -> C (Hs.Pat ())
compileErasedConP ty s ps = compilePats ty ps >>= \case
  [p] -> addPatBang s p
  _   -> __IMPOSSIBLE__

compileLitPat :: Literal -> C (Hs.Pat ())
compileLitPat = \case
  LitChar c -> return $ Hs.charP c
  l -> agda2hsErrorM $ "bad literal pattern:" <?> prettyTCM l

compileTupleConP :: Type -> Hs.Boxed -> NAPs -> C (Hs.Pat ())
compileTupleConP ty b ps = do
  ps <- compilePats ty ps
  return $ Hs.PTuple () b ps

-- Local (where) declarations ---------------------------------------------


-- TODO: simplify this when Agda exposes where-provenance in 'Internal' syntax
-- | Run a computation with all the local declarations in the state.
withFunctionLocals :: QName -> C a -> C a
withFunctionLocals q k = do
  ls <- takeWhile (isAnonymousModuleName . qnameModule)
      . dropWhile (<= q)
      . map fst
      . filter (usableModality . getModality . snd) -- drop if it's an erased definition anyway
      . sortDefs <$> liftTCM curDefs
  reportSDoc "agda2hs.compile.locals" 17 $ "Function locals: "<+> prettyTCM ls
  withLocals ls k


-- | Filter local declarations that belong to the given module.
zoomLocals :: ModuleName -> LocalDecls -> LocalDecls
zoomLocals mname = filter ((mname `isLeParentModuleOf`) . qnameModule)


-- | Before checking a clause, grab all of its local declarations.
-- TODO: simplify this when Agda exposes where-provenance in 'Internal' syntax
withClauseLocals :: ModuleName -> Clause -> C a -> C a
withClauseLocals curModule c@Clause{..} k = do
  ls <- asks locals
  let
    uses = filter
      (  (curModule `isFatherModuleOf`) . qnameModule
      \/ (`extLamUsedIn` c) )
      (getLocalUses ls c)
    nonExtLamUses = qnameModule <$> filter (not . isExtendedLambdaName) uses
    whereModuleName
      | null uses = Nothing
      | otherwise = Just $ case nonExtLamUses ++ [curModule] of
          (x:_) -> x
          _ -> __IMPOSSIBLE__
    ls' = case whereModuleName of
      Nothing -> []
      Just m  -> zoomLocals m ls
  reportSDoc "agda2hs.compile.locals" 18 $ "Clause locals: "<+> prettyTCM ls'
  withLocals ls' k


-- | Ensure a definition can be defined as transparent.
checkTransparentPragma :: Definition -> C ()
checkTransparentPragma def = do
  whenM (andM [emitsRtc $ defName def, not <$> checkNoneErased tele alternatingLevels]) $ genericDocError =<<
        "Cannot make function" <+> prettyTCM (defName def) <+> "transparent." <+>
        "Transparent functions cannot have erased arguments with runtime checking."
  compiledFun <- defn <$> compileFun False def
  case compiledFun of
    [Hs.FunBind _ cls] ->
      mapM_ checkTransparentClause cls
    [Hs.TypeDecl _ hd b] ->
      checkTransparentTypeDef hd b
    _ -> __IMPOSSIBLE__
  where
    tele = theTel $ telView' $ defType def

    checkTransparentClause :: Hs.Match () -> C ()
    checkTransparentClause = \case
      Hs.Match _ _ [p] (Hs.UnGuardedRhs _ e) _ | patToExp p == Just e -> return ()
      _ -> errNotTransparent

    checkTransparentTypeDef :: Hs.DeclHead () -> Hs.Type () -> C ()
    checkTransparentTypeDef (Hs.DHApp _ _ (Hs.UnkindedVar _ x)) (Hs.TyVar _ y) | x == y = return ()
    checkTransparentTypeDef _ _ = errNotTransparent

    errNotTransparent = agda2hsErrorM $
      "Cannot make function" <+> prettyTCM (defName def) <+> "transparent." <+>
      "A transparent function must have exactly one non-erased argument and return it unchanged."


-- | Ensure a definition can be defined as inline.
checkInlinePragma :: Definition -> C ()
checkInlinePragma def@Defn{defName = f, defType = ty} = do
  let Function{funClauses = cs} = theDef def
      typeTel = theTel $ telView' ty
  whenM (andM [emitsRtc $ defName def, not <$> checkNoneErased typeTel alternatingLevels]) $ genericDocError =<<
        "Cannot make function" <+> prettyTCM (defName def) <+> "inlinable." <+>
        "Inline functions cannot have erased arguments with runtime checking."
  case filter (isJust . clauseBody) cs of
    [c] ->
      unlessM (allowedPats (namedClausePats c)) $ agda2hsErrorM $
        "Cannot make function" <+> prettyTCM (defName def) <+> "inlinable." <+>
        "Inline functions can only use variable patterns or transparent record constructor patterns."
    _ ->
      agda2hsErrorM $
        "Cannot make function" <+> prettyTCM f <+> "inlinable." <+>
        "An inline function must have exactly one clause."

  where allowedPat :: DeBruijnPattern -> C Bool
        allowedPat VarP{} = pure True
        -- only allow matching on (unboxed) record constructors
        allowedPat (ConP ch ci cargs) =
          isUnboxConstructor (conName ch) >>= \case
            Just _  -> allowedPats cargs
            Nothing -> pure False
        allowedPat _ = pure False

        allowedPats :: NAPs -> C Bool
        allowedPats pats = allM (allowedPat . dget . dget) pats
