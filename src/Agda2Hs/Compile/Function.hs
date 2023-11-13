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
import Agda.Syntax.Literal
import Agda.Syntax.Common.Pretty ( prettyShow )
import Agda.Syntax.Scope.Monad ( isDatatypeModule )

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope ( telView )
import Agda.TypeChecking.Sort ( ifIsSort )

import Agda.Utils.Functor ( (<&>) )
import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name ( compileQName )
import Agda2Hs.Compile.Term ( compileTerm, compileVar )
import Agda2Hs.Compile.Type ( compileTopLevelType )
import Agda2Hs.Compile.TypeDefinition ( compileTypeDef )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils
import Agda.TypeChecking.Datatypes (isDataOrRecord)

isSpecialPat :: QName -> Maybe (ConHead -> ConPatternInfo -> [NamedArg DeBruijnPattern] -> C (Hs.Pat ()))
isSpecialPat qn = case prettyShow qn of
  "Haskell.Prim.Tuple._;_" -> Just tuplePat
  "Agda.Builtin.Int.Int.pos" -> Just posIntPat
  "Agda.Builtin.Int.Int.negsuc" -> Just negSucIntPat
  s | s `elem` badConstructors -> Just $ \ _ _ _ -> genericDocError =<<
    "constructor `" <> prettyTCM qn <> "` not supported in patterns"
  _ -> Nothing
  where
    badConstructors =
      [ "Agda.Builtin.Nat.Nat.zero"
      , "Agda.Builtin.Nat.Nat.suc"
      ]

isUnboxCopattern :: DeBruijnPattern -> C Bool
isUnboxCopattern (ProjP _ q) = isJust <$> isUnboxProjection q
isUnboxCopattern _           = return False

tuplePat :: ConHead -> ConPatternInfo -> [NamedArg DeBruijnPattern] -> C (Hs.Pat ())
tuplePat cons i ps = do
  let p = ConP cons i ps
      err = sep [ "Tuple pattern"
                , nest 2 $ prettyTCM p
                , "does not have a known size." ]
  xs <- makeListP' "Agda.Builtin.Unit.tt" "Haskell.Prim.Tuple._;_" err p
  qs <- mapM compilePat xs
  return $ Hs.PTuple () Hs.Boxed qs

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

posIntPat :: ConHead -> ConPatternInfo -> [NamedArg DeBruijnPattern] -> C (Hs.Pat ())
posIntPat c i [p] = do
  n <- compileLitNatPat (namedArg p)
  return $ Hs.PLit () (Hs.Signless ()) (Hs.Int () n (show n))
posIntPat _ _ _ = __IMPOSSIBLE__

negSucIntPat :: ConHead -> ConPatternInfo -> [NamedArg DeBruijnPattern] -> C (Hs.Pat ())
negSucIntPat c i [p] = do
  n <- (1+) <$> compileLitNatPat (namedArg p)
  return $ Hs.PLit () (Hs.Negative ()) (Hs.Int () n (show (negate n)))
negSucIntPat _ _ _ = __IMPOSSIBLE__

-- The bool argument says whether we also want the type signature or just the body
compileFun, compileFun' :: Bool -> Definition -> C [Hs.Decl ()]
-- initialize locals when first stepping into a function
compileFun withSig def@Defn{..} = withFunctionLocals defName $ compileFun' withSig def
-- inherit existing (instantiated) locals
compileFun' withSig def@(Defn {..}) = do
  reportSDoc "agda2hs.compile" 6 $ "Compiling function: " <+> prettyTCM defName
  when withSig $ whenJustM (liftTCM $ isDatatypeModule $ qnameModule defName) $ \_ ->
    genericDocError =<< text "not supported by agda2hs: functions inside a record module"
  let keepClause = maybe False keepArg . clauseType
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
        cs <- mapMaybeM (compileClause (qnameModule defName) x) clauses

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

compileClause :: ModuleName -> Hs.Name () -> Clause -> C (Maybe (Hs.Match ()))
compileClause mod x c = withClauseLocals mod c $ compileClause' mod x c

compileClause' :: ModuleName -> Hs.Name () -> Clause -> C (Maybe (Hs.Match ()))
compileClause' curModule x c@Clause{clauseBody = Nothing} = pure Nothing
compileClause' curModule x c@Clause{..} = do
  reportSDoc "agda2hs.compile" 7 $ "compiling clause: " <+> prettyTCM c
  reportSDoc "agda2hs.compile" 17 $ "Old context: " <+> (prettyTCM =<< getContext)
  reportSDoc "agda2hs.compile" 17 $ "Clause telescope: " <+> prettyTCM clauseTel
  addContext (KeepNames clauseTel) $ do
    ps <- compilePats namedClausePats
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
    body <- inWhereModule $ compileTerm $ fromMaybe __IMPOSSIBLE__ clauseBody
    let rhs = Hs.UnGuardedRhs () body
        whereBinds | null whereDecls = Nothing
                   | otherwise       = Just $ Hs.BDecls () (concat whereDecls)
        match = case (x, ps) of
          (Hs.Symbol{}, p : q : ps) -> Hs.InfixMatch () p x (q : ps) rhs whereBinds
          _                         -> Hs.Match () x ps rhs whereBinds
    return $ Just match

noAsPatterns :: DeBruijnPattern -> C ()
noAsPatterns = \case
    VarP i _ -> checkPatternInfo i
    DotP i _ -> checkPatternInfo i
    ConP _ cpi ps -> do
      checkPatternInfo $ conPInfo cpi
      forM_ ps $ noAsPatterns . namedArg
    LitP i _ -> checkPatternInfo i
    ProjP{} -> return ()
    IApplyP i _ _ _ -> checkPatternInfo i
    DefP i _ ps -> do
      checkPatternInfo i
      forM_ ps $ noAsPatterns . namedArg
  where
    checkPatternInfo i = unless (null $ patAsNames i) $
      genericDocError =<< "not supported by agda2hs: as patterns"

compilePats :: NAPs -> C [Hs.Pat ()]
compilePats ps = mapM (compilePat . namedArg) =<< filterM keepPat ps
  where
    keepPat :: NamedArg DeBruijnPattern -> C Bool
    keepPat p = do
      keep <- return (keepArg p) `and2M` (not <$> isUnboxCopattern (namedArg p))
      when keep $ noAsPatterns $ namedArg p
      -- We do not allow forced (dot) patterns for non-erased arguments (see issue #142).
      when (usableModality p && isForcedPat (namedArg p)) $
        genericDocError =<< "not supported by agda2hs: forced (dot) patterns in non-erased positions"
      return keep

    isForcedPat :: DeBruijnPattern -> Bool
    isForcedPat = \case
      VarP{}        -> False
      DotP{}        -> True
      ConP c cpi ps -> conPLazy cpi
      LitP{}        -> False
      ProjP{}       -> False
      IApplyP{}     -> False
      DefP{}        -> False


compilePat :: DeBruijnPattern -> C (Hs.Pat ())
compilePat p@(VarP o x)
  | PatOWild <- patOrigin o = return $ Hs.PWildCard ()
  | otherwise               = do
      n <- hsName <$> compileVar (dbPatVarIndex x)
      checkValidVarName n
      return $ Hs.PVar () n
compilePat (ConP h i ps)
  | Just semantics <- isSpecialPat (conName h) = setCurrentRange h $ semantics h i ps
compilePat (ConP h _ ps) = isUnboxConstructor (conName h) >>= \case
  Just s -> compileErasedConP ps >>= addPatBang s
  Nothing -> do
    ps <- compilePats ps
    c <- compileQName (conName h)
    return $ pApp c ps
compilePat (LitP _ l) = compileLitPat l
compilePat (ProjP _ q) = do
  reportSDoc "agda2hs.compile" 6 $ "compiling copattern: " <+> text (prettyShow q)
  unlessM (asks copatternsEnabled) $
    genericDocError =<< "not supported in Haskell: copatterns"
  let x = hsName $ prettyShow q
  return $ Hs.PVar () x
compilePat p = genericDocError =<< "bad pattern:" <?> prettyTCM p

compileErasedConP :: NAPs -> C (Hs.Pat ())
compileErasedConP ps = compilePats ps <&> \case
  [p] -> p
  _   -> __IMPOSSIBLE__

compileLitPat :: Literal -> C (Hs.Pat ())
compileLitPat = \case
  LitChar c -> return $ Hs.charP c
  l -> genericDocError =<< "bad literal pattern:" <?> prettyTCM l

-- Local (where) declarations ---------------------------------------------

-- | Before checking a function, grab all of its local declarations.
-- TODO: simplify this when Agda exposes where-provenance in 'Internal' syntax
withFunctionLocals :: QName -> C a -> C a
withFunctionLocals q k = do
  ls <- takeWhile (isAnonymousModuleName . qnameModule)
      . dropWhile (<= q)
      . map fst
      . filter (usableModality . getModality . snd) -- drop if it's an erased definition anyway
      . sortDefs <$> liftTCM curDefs
  reportSDoc "agda2hs.compile.locals" 17 $ "Function locals: "<+> prettyTCM ls
  withLocals ls k

-- | Retain only those local declarations that belong to current clause's module.
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
