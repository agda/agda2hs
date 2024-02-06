{-# LANGUAGE OverloadedStrings #-}
module Agda2Hs.Compile.Function where

import Control.Monad ( (>=>), filterM, forM_ )
import Control.Monad.Reader ( asks )

import Data.Generics
import Data.List
import Data.Maybe ( fromMaybe, isJust )
import qualified Data.Text as Text

import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Build as Hs

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
import Agda.TypeChecking.Telescope ( telView, mustBePi, piApplyM )
import Agda.TypeChecking.Sort ( ifIsSort )
import Agda.TypeChecking.Datatypes ( getConType )
import Agda.TypeChecking.Records ( getDefType )
import Agda.TypeChecking.Reduce ( reduce )

import Agda.Utils.Functor ( (<&>), dget)
import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.Lens ((^.))
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name ( compileQName )
import Agda2Hs.Compile.Term ( compileTerm, usableDom )
import Agda2Hs.Compile.Type ( compileTopLevelType, compiledDom, DomOutput(..) )
import Agda2Hs.Compile.TypeDefinition ( compileTypeDef )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.Compile.Var ( compileDBVar )
import Agda2Hs.HsUtils
import Agda.TypeChecking.Datatypes (isDataOrRecord)


-- | Compilation rules for specific constructors in patterns.
isSpecialCon :: QName -> Maybe (Type -> NAPs -> C (Hs.Pat ()))
isSpecialCon qn = case prettyShow qn of
  s | s `elem` badConstructors     -> Just itsBad
  "Haskell.Prim.Tuple._,_"         -> Just tuplePat
  "Haskell.Prim.Tuple._×_×_._,_,_" -> Just tuplePat
  "Haskell.Extra.Erase.Erased"     -> Just tuplePat
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
    itsBad _ _ = genericDocError =<< "constructor `" <> prettyTCM qn <> "` not supported in patterns"

-- | Translate list of patterns into a Haskell n-uple pattern.
tuplePat :: Type -> NAPs -> C (Hs.Pat ())
tuplePat ty ps =
  compilePats ty ps
  <&> Hs.PTuple () Hs.Boxed

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
  p -> genericDocError =<< "not a literal natural number pattern:" <?> prettyTCM p


compileFun, compileFun'
  :: Bool -- ^ Whether the type signature shuuld also be generated
  -> Definition -> C [Hs.Decl ()]

compileFun withSig def@Defn{..} =
  setCurrentRangeQ defName 
    $ maybePrependFixity defName (defName ^. lensFixity)
    -- initialize locals when first stepping into a function
    $ withFunctionLocals defName
    $ compileFun' withSig def

-- inherit existing (instantiated) locals
compileFun' withSig def@Defn{..} = do
  reportSDoc "agda2hs.compile" 6 $ "Compiling function: " <+> prettyTCM defName

  whenM ((withSig &&) <$> inRecordMod defName) $
    genericDocError =<< text "not supported by agda2hs: functions inside a record module"

  withCurrentModule m $ do
    ifM (endsInSort defType)
        -- if the function type ends in Sort, it's a type alias!
        (ensureNoLocals err >> compileTypeDef x def) 
        -- otherwise, we have to compile clauses.
        $ do

      when withSig $ checkValidFunName x

      compileTopLevelType withSig defType $ \ty -> do

        let filtered = filter keepClause funClauses
        weAreOnTop <- isJust <$> liftTCM  (currentModule >>= isTopLevelModule)
        pars <- getContextArgs

        -- We only instantiate the clauses to the current module parameters
        -- if the current module isn't the toplevel module
        unless weAreOnTop $
          reportSDoc "agda2hs.compile.type" 6 $ "Applying module parameters to clauses: " <+> prettyTCM pars
        let clauses = if weAreOnTop then filtered else filtered `apply` pars

        typ <- if weAreOnTop then pure defType else piApplyM defType pars


        -- TODO(flupe):
        -- for projection-like functions, patterns only start at the record argument
        -- so it is incorrect to use defType as a way to discard patterns, as they are not aligned

        cs  <- mapMaybeM (compileClause (qnameModule defName) x typ) clauses

        when (null cs) $ genericDocError
          =<< text "Functions defined with absurd patterns exclusively are not supported."
          <+> text "Use function `error` from the Haskell.Prelude instead."

        return $ [Hs.TypeSig () [x] ty | withSig ] ++ [Hs.FunBind () cs]
  where
    Function{..} = theDef
    m = qnameModule defName
    n = qnameName defName
    x = hsName $ prettyShow n
    endsInSort t = do
      TelV tel b <- telView t
      addContext tel $ ifIsSort b (\_ -> return True) (return False)
    err = "Not supported: type definition with `where` clauses"


compileClause :: ModuleName -> Hs.Name () -> Type -> Clause -> C (Maybe (Hs.Match ()))
compileClause mod x t c = withClauseLocals mod c $ compileClause' mod x t c

compileClause' :: ModuleName -> Hs.Name () -> Type -> Clause -> C (Maybe (Hs.Match ()))
compileClause' curModule x _  c@Clause{clauseBody = Nothing} = pure Nothing
compileClause' curModule x ty c@Clause{..} = do
  reportSDoc "agda2hs.compile" 7  $ "compiling clause: " <+> prettyTCM c
  reportSDoc "agda2hs.compile" 17 $ "Old context: "      <+> (prettyTCM =<< getContext)
  reportSDoc "agda2hs.compile" 17 $ "Clause telescope: " <+> prettyTCM clauseTel
  reportSDoc "agda2hs.compile" 17 $ "Clause type:      " <+> prettyTCM clauseType
  reportSDoc "agda2hs.compile" 17 $ "Function type:    " <+> prettyTCM ty
  reportSDoc "agda2hs.compile" 17 $ "Clause patterns:  " <+> text (prettyShow namedClausePats)

  addContext (KeepNames clauseTel) $ do

    ps <- compilePats ty namedClausePats

    let isWhereDecl = not . isExtendedLambdaName
          /\ (curModule `isFatherModuleOf`) . qnameModule
    children <- filter isWhereDecl <$> asks locals
    whereDecls <- mapM (getConstInfo >=> compileFun' True) children

    -- Jesper, 2023-10-30: We should compile the body in the module of the
    -- `where` declarations (if there are any) in order to drop the arguments
    -- that correspond to the pattern variables of this clause from the calls to
    -- the functions defined in the `where` block.
    let inWhereModule = case children of
          [] -> id
          (c:_) -> withCurrentModule $ qnameModule c

    let Just body            = clauseBody
        Just (unArg -> typ)  = clauseType

    hsBody <- inWhereModule $ compileTerm typ body

    let rhs = Hs.UnGuardedRhs () hsBody
        whereBinds | null whereDecls = Nothing
                   | otherwise       = Just $ Hs.BDecls () (concat whereDecls)
        match = case (x, ps) of
          (Hs.Symbol{}, p : q : ps) -> Hs.InfixMatch () p x (q : ps) rhs whereBinds
          _                         -> Hs.Match () x ps rhs whereBinds
    return $ Just match


-- TODO(flupe): projection-like definitions are missing the first (variable) patterns
--             (that are however present in the type)
--             so we should drop the first parameters in the input type (using funProjection.projLams)
-- TODO(flupe): handle copatterns (that don't expect a Pi type) (See Unbox:sort2)
compilePats :: Type -> NAPs -> C [Hs.Pat ()]
compilePats _ [] = pure []
compilePats ty ((namedArg -> ProjP po pn):ps) = do
  reportSDoc "agda2hs.compile" 6 $ "compiling copattern: " <+> text (prettyShow pn)
  -- NOTE: should be fine for unboxed records
  unlessM (asks copatternsEnabled `or2M` (isJust <$> isUnboxProjection pn)) $
    genericDocError =<< "not supported in Haskell: copatterns"
  Just (unEl -> Pi a b) <- getDefType pn ty -- ????
  compilePats (absBody b) ps


-- -- copatterns patterns
-- compilePat ty (ProjP _ q) = do
--   reportSDoc "agda2hs.compile" 6 $ "compiling copattern: " <+> text (prettyShow q)
--   unlessM (asks copatternsEnabled) $
--     genericDocError =<< "not supported in Haskell: copatterns"
--   let x = hsName $ prettyShow q
--   return $ Hs.PVar () x

compilePats ty ((namedArg -> pat):ps) = do
  (a, b) <- mustBePi ty
  reportSDoc "agda2hs.compile.pattern" 5 $ text "Compiling pattern:" <+> prettyTCM pat
  let rest = compilePats (absApp b (patternToTerm pat)) ps
  compiledDom a >>= \case
    DOInstance -> rest
    DODropped  -> rest <* when (usableDom a) checkForced
    DOKept     -> do
      checkForced
      checkNoAsPatterns pat
      (:) <$> compilePat (unDom a) pat <*> rest
  where checkForced  = when (isForcedPat pat) $ genericDocError =<< "not supported by agda2hs: forced (dot) patterns in non-erased positions"


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

  case isSpecialCon (conName ch) of
    Just semantics -> setCurrentRange ch $ semantics ty ps
    Nothing -> do
      isUnboxConstructor (conName ch) >>= \case
        Just s -> compileErasedConP ty ps >>= addPatBang s
        Nothing -> do
          ps <- compilePats ty ps
          c <- compileQName (conName ch)
          return $ pApp c ps

-- literal patterns
compilePat ty (LitP _ l) = compileLitPat l


-- nothing else is supported
compilePat _ p = genericDocError =<< "bad pattern:" <?> prettyTCM p


compileErasedConP :: Type -> NAPs -> C (Hs.Pat ())
compileErasedConP ty ps = compilePats ty ps <&> \case
  [p] -> p
  _   -> __IMPOSSIBLE__

compileLitPat :: Literal -> C (Hs.Pat ())
compileLitPat = \case
  LitChar c -> return $ Hs.charP c
  l -> genericDocError =<< "bad literal pattern:" <?> prettyTCM l


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
      | otherwise = Just $ head (nonExtLamUses ++ [curModule])
    ls' = case whereModuleName of
      Nothing -> []
      Just m  -> zoomLocals m ls
  reportSDoc "agda2hs.compile.locals" 18 $ "Clause locals: "<+> prettyTCM ls'
  withLocals ls' k


-- | Ensure a definition can be defined as transparent.
checkTransparentPragma :: Definition -> C ()
checkTransparentPragma def = compileFun False def >>= \case
    [Hs.FunBind _ cls] ->
      mapM_ checkTransparentClause cls
    [Hs.TypeDecl _ hd b] ->
      checkTransparentTypeDef hd b
    _ -> __IMPOSSIBLE__
  where
    checkTransparentClause :: Hs.Match () -> C ()
    checkTransparentClause = \case
      Hs.Match _ _ [p] (Hs.UnGuardedRhs _ e) _ | patToExp p == Just e -> return ()
      _ -> errNotTransparent

    checkTransparentTypeDef :: Hs.DeclHead () -> Hs.Type () -> C ()
    checkTransparentTypeDef (Hs.DHApp _ _ (Hs.UnkindedVar _ x)) (Hs.TyVar _ y) | x == y = return ()
    checkTransparentTypeDef _ _ = errNotTransparent

    errNotTransparent = genericDocError =<<
      "Cannot make function" <+> prettyTCM (defName def) <+> "transparent." <+>
      "A transparent function must have exactly one non-erased argument and return it unchanged."


-- | Ensure a definition can be defined as inline.
checkInlinePragma :: Definition -> C ()
checkInlinePragma def@Defn{defName = f} = do
  let Function{funClauses = cs} = theDef def
  case filter (isJust . clauseBody) cs of
    [c] ->
      unlessM (allowedPats (namedClausePats c)) $ genericDocError =<<
        "Cannot make function" <+> prettyTCM (defName def) <+> "inlinable." <+>
        "Inline functions can only use variable patterns or transparent record constructor patterns."
    _ ->
      genericDocError =<<
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
        allowedPats pats = allM pats (allowedPat . dget . dget)
