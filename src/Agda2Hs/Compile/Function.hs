module Agda2Hs.Compile.Function where

import Control.Arrow ( Arrow((***), second), (>>>) )
import Control.Monad ( (>=>), foldM, filterM, forM_ )
import Control.Monad.Reader ( asks )

import Data.Generics
import Data.List
import Data.Maybe ( fromMaybe, isJust )
import qualified Data.Text as Text

import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Build as Hs

import Agda.Compiler.Backend
import Agda.Compiler.Common

import Agda.Syntax.Common ( NamedArg, namedArg )
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.Syntax.Scope.Base ( BindingSource(LambdaBound) )
import Agda.Syntax.Scope.Monad ( bindVariable )

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope ( telView, teleArgs, piApplyM )
import Agda.TypeChecking.Sort ( ifIsSort )

import Agda.Utils.Functor ( (<&>) )
import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.Pretty ( prettyShow )
import Agda.Utils.List ( snoc )
import Agda.Utils.Monad

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name ( compileQName )
import Agda2Hs.Compile.Term ( compileTerm, compileVar )
import Agda2Hs.Compile.Type ( compileTopLevelType )
import Agda2Hs.Compile.TypeDefinition ( compileTypeDef )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

isSpecialPat :: QName -> Maybe (ConHead -> ConPatternInfo -> [NamedArg DeBruijnPattern] -> C (Hs.Pat ()))
isSpecialPat = prettyShow >>> \ case
  "Haskell.Prim.Tuple._;_" -> Just tuplePat
  "Agda.Builtin.Int.Int.pos" -> Just posIntPat
  "Agda.Builtin.Int.Int.negsuc" -> Just negSucIntPat
  "Agda.Builtin.Nat.Nat.zero" -> Just zeroNatPat
  "Agda.Builtin.Nat.Nat.suc" -> Just sucNatPat
  _ -> Nothing

isUnboxCopattern :: DeBruijnPattern -> C Bool
isUnboxCopattern (ProjP _ q) = isJust <$> isUnboxProjection q
isUnboxCopattern _           = return False

tuplePat :: ConHead -> ConPatternInfo -> [NamedArg DeBruijnPattern] -> C (Hs.Pat ())
tuplePat cons i ps = do
  let p = ConP cons i ps
      err = sep [ text "Tuple pattern"
                , nest 2 $ prettyTCM p
                , text "does not have a known size." ]
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
  p -> genericDocError =<< text "not a literal natural number pattern:" <?> prettyTCM p

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

zeroNatPat :: ConHead -> ConPatternInfo -> [NamedArg DeBruijnPattern] -> C (Hs.Pat ())
zeroNatPat _ _ _ = return $ Hs.PLit () (Hs.Signless ()) (Hs.Int () 0 "0")

sucNatPat :: ConHead -> ConPatternInfo -> [NamedArg DeBruijnPattern] -> C (Hs.Pat ())
sucNatPat _ _ [p] = do
  n <- (1+) <$> compileLitNatPat (namedArg p)
  return $ Hs.PLit () (Hs.Signless ()) (Hs.Int () n (show n))
sucNatPat _ _ _ = __IMPOSSIBLE__

-- The bool argument says whether we also want the type signature or just the body
compileFun, compileFun' :: Bool -> Definition -> C [Hs.Decl ()]
-- initialize locals when first stepping into a function
compileFun withSig def@Defn{..} = withFunctionLocals defName $ compileFun' withSig def
-- inherit existing (instantiated) locals
compileFun' withSig def@(Defn {..}) = do
  reportSDoc "agda2hs.compile" 6 $ text "compiling function: " <+> prettyTCM defName
  let keepClause = maybe False keepArg . clauseType
  withCurrentModule m $ setCurrentRange (nameBindingSite n) $ do
    ifM (endsInSort defType) (ensureNoLocals err >> compileTypeDef x def) $ do
      when withSig $ checkValidFunName x
      compileTopLevelType defType $ \ty -> do
        -- Instantiate the clauses to the current module parameters
        pars <- getContextArgs
        reportSDoc "agda2hs.compile" 10 $ text "applying clauses to parameters: " <+> prettyTCM pars
        let clauses = filter keepClause funClauses `apply` pars
        cs <- mapM (compileClause (qnameModule defName) x) clauses
        return $ [Hs.TypeSig () [x] ty | withSig ] ++ [ Hs.FunBind () cs]
  where
    Function{..} = theDef
    m = qnameModule defName
    n = qnameName defName
    x = hsName $ prettyShow n
    endsInSort t = do
      TelV tel b <- telView t
      addContext tel $ ifIsSort b (\_ -> return True) (return False)
    err = "Not supported: type definition with `where` clauses"

compileClause :: ModuleName -> Hs.Name () -> Clause -> C (Hs.Match ())
compileClause curModule x c@Clause{..} = withClauseLocals curModule c $ do
  reportSDoc "agda2hs.compile" 7 $ text "compiling clause: " <+> prettyTCM c
  addContext (KeepNames clauseTel) $ do
    forM_ namedClausePats $ noAsPatterns . namedArg
    ps <- compilePats namedClausePats
    ls <- asks locals
    let
      (children, ls') = partition
        (   not . isExtendedLambdaName
         /\ (curModule `isFatherModuleOf`) . qnameModule )
        ls
    withLocals ls' $ do
      body <- compileTerm $ fromMaybe __IMPOSSIBLE__ clauseBody
      whereDecls <- mapM (getConstInfo >=> compileFun' True) children
      let rhs = Hs.UnGuardedRhs () body
          whereBinds | null whereDecls = Nothing
                     | otherwise       = Just $ Hs.BDecls () (concat whereDecls)
          match = case (x, ps) of
            (Hs.Symbol{}, p : q : ps) -> Hs.InfixMatch () p x (q : ps) rhs whereBinds
            _                         -> Hs.Match () x ps rhs whereBinds
      return match

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
      genericDocError =<< text "not supported by Agda2Hs: as patterns"

compilePats :: NAPs -> C [Hs.Pat ()]
compilePats ps = mapM (compilePat . namedArg) =<< filterM keepPat ps
  where
    keepPat :: NamedArg DeBruijnPattern -> C Bool
    keepPat p = andM
      [ return $ keepArg p
      , not <$> isUnboxCopattern (namedArg p)
      ]

compilePat :: DeBruijnPattern -> C (Hs.Pat ())
compilePat p@(VarP o x)
  | PatOWild <- patOrigin o = return $ Hs.PWildCard ()
  | otherwise               = do
      n <- hsName <$> compileVar (dbPatVarIndex x)
      checkValidVarName n
      return $ Hs.PVar () n
compilePat (ConP h i ps)
  | Just semantics <- isSpecialPat (conName h) = setCurrentRange h $ semantics h i ps
compilePat (ConP h _ ps) = isUnboxConstructor (conName h) >>= \ case
  Just s -> addPatBang s <$> compileErasedConP ps
  Nothing -> do
    ps <- compilePats ps
    c <- compileQName (conName h)
    return $ pApp c ps
compilePat (LitP _ l) = compileLitPat l
compilePat (ProjP _ q) = do
  reportSDoc "agda2hs.compile" 6 $ text "compiling copattern: " <+> text (prettyShow q)
  unlessM (asks isCompilingInstance) $
    genericDocError =<< text "not supported in Haskell: copatterns"
  let x = hsName $ prettyShow q
  return $ Hs.PVar () x
compilePat p = genericDocError =<< text "bad pattern:" <?> prettyTCM p

compileErasedConP :: NAPs -> C (Hs.Pat ())
compileErasedConP ps = compilePats ps <&> \case
  [p] -> p
  _   -> __IMPOSSIBLE__

compileLitPat :: Literal -> C (Hs.Pat ())
compileLitPat = \case
  LitChar c -> return $ Hs.charP c
  l -> genericDocError =<< text "bad literal pattern:" <?> prettyTCM l

-- Local (where) declarations ---------------------------------------------

-- | Before checking a function, grab all of its local declarations.
-- TODO: simplify this when Agda exposes where-provenance in 'Internal' syntax
withFunctionLocals :: QName -> C a -> C a
withFunctionLocals q k = do
  ls <- takeWhile (isAnonymousModuleName . qnameModule)
      . dropWhile (<= q)
      . map fst
      . sortDefs <$> liftTCM curDefs
  withLocals ls k

-- | Retain only those local declarations that belong to current clause's module.
zoomLocals :: ModuleName -> LocalDecls -> LocalDecls
zoomLocals mname = filter ((mname `isLeParentModuleOf`) . qnameModule)

-- | Before checking a clause, grab all of its local declarationaas.
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

    errNotTransparent = genericError $
      "A transparent function must have exactly one non-erased argument and return it unchanged."
