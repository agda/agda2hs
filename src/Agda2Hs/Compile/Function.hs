module Agda2Hs.Compile.Function where

import Control.Arrow ( Arrow((***), second), (>>>) )
import Control.Monad ( (>=>), foldM, filterM )
import Control.Monad.Reader ( asks )

import Data.Generics
import Data.List
import Data.Maybe ( fromMaybe )

import qualified Language.Haskell.Exts.Syntax as Hs

import Agda.Compiler.Backend
import Agda.Compiler.Common

import Agda.Syntax.Common ( NamedArg, namedArg )
import Agda.Syntax.Internal
import Agda.Syntax.Scope.Base ( BindingSource(LambdaBound) )
import Agda.Syntax.Scope.Monad ( bindVariable )

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute ( TelV(TelV) )
import Agda.TypeChecking.Telescope ( telView, teleArgs )
import Agda.TypeChecking.Sort ( ifIsSort )

import Agda.Utils.Pretty ( prettyShow )
import Agda.Utils.List ( snoc )
import Agda.Utils.Monad

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name ( hsQName )
import Agda2Hs.Compile.Term ( compileTerm )
import Agda2Hs.Compile.Type ( compileType )
import Agda2Hs.Compile.TypeDefinition ( compileTypeDef )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

isSpecialPat :: QName -> Maybe (ConHead -> ConPatternInfo -> [NamedArg DeBruijnPattern] -> C (Hs.Pat ()))
isSpecialPat = prettyShow >>> \ case
  "Haskell.Prim.Tuple._;_" -> Just tuplePat
  _ -> Nothing

isUnboxCopattern :: DeBruijnPattern -> C Bool
isUnboxCopattern (ProjP _ q) = isUnboxProjection q
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

compileFun, compileFun' :: Definition -> C [Hs.Decl ()]
-- initialize locals when first stepping into a function
compileFun def@Defn{..} = withFunctionLocals defName $ compileFun' def
-- inherit existing (instantiated) locals
compileFun' def@(Defn {..}) = do
  let m = qnameModule defName
      n = qnameName defName
      x = hsName $ prettyShow n
  reportSDoc "agda2hs.compile" 6 $ text "compiling function: " <+> prettyTCM defName
  let keepClause = maybe False keepArg . clauseType
  withCurrentModule m $ setCurrentRange (nameBindingSite n) $ do
    ifM (endsInSort defType) (ensureNoLocals err >> compileTypeDef x def) $ do
      ty <- compileType (unEl defType)
      cs <- mapM (compileClause (qnameModule defName) x) (filter keepClause funClauses)
      return [Hs.TypeSig () [x] ty, Hs.FunBind () cs]
  where
    Function{..} = theDef
    endsInSort t = do
      TelV tel b <- telView t
      addContext tel $ ifIsSort b (\_ -> return True) (return False)
    err = "Not supported: type definition with `where` clauses"

compileClause :: ModuleName -> Hs.Name () -> Clause -> C (Hs.Match ())
compileClause curModule x c@Clause{..} = withClauseLocals curModule c $ do
  addContext (KeepNames clauseTel) $ liftTCM1 localScope $ do
    scopeBindPatternVariables namedClausePats
    ps <- compilePats namedClausePats
    ls0 <- asks locals
    let
      tArgs = teleArgs clauseTel
      shrinkDefs :: Data a => a -> a
      shrinkDefs = everywhere $ mkT go
        where go t | Def q es <- t, q `elem` map fst ls0
                   = Def q (drop (length tArgs) es)
                   | otherwise = t
      body' = shrinkDefs <$> clauseBody
      ls    = map (second (mapDef shrinkDefs . (`applyUnderTele` tArgs))) ls0
      (children, ls') = partition
        (   not . isExtendedLambdaName . fst
         /\ (curModule `isFatherModuleOf`) . qnameModule . fst )
        ls
    withLocals ls' $ do
      body <- fromMaybe (hsError $ pp x ++ ": impossible") <$> mapM compileTerm body'
      whereDecls <- mapM compileFun' (snd <$> children)
      let rhs = Hs.UnGuardedRhs () body
          whereBinds | null whereDecls = Nothing
                     | otherwise       = Just $ Hs.BDecls () (concat whereDecls)
          match = case (x, ps) of
            (Hs.Symbol{}, p : q : ps) -> Hs.InfixMatch () p x (q : ps) rhs whereBinds
            _                         -> Hs.Match () x ps rhs whereBinds
      return match

-- | When going under a binder we need to update the scope as well as the context in order to get
-- correct printing of variable names (Issue #14).
scopeBindPatternVariables :: NAPs -> C ()
scopeBindPatternVariables = mapM_ (scopeBind . namedArg)
  where
    scopeBind :: DeBruijnPattern -> C ()
    scopeBind = \ case
      VarP o i | PatOVar x <- patOrigin o -> liftTCM $ bindVariable LambdaBound (nameConcrete x) x
               | otherwise                -> return ()
      ConP _ _ ps -> scopeBindPatternVariables ps
      DotP{}      -> return ()
      LitP{}      -> return ()
      ProjP{}     -> return ()
      IApplyP{}   -> return ()
      DefP{}      -> return ()

compilePats :: NAPs -> C [Hs.Pat ()]
compilePats ps = mapM (compilePat . namedArg) =<< filterM keepPat ps
  where
    keepPat :: NamedArg DeBruijnPattern -> C Bool
    keepPat p = andM
      [ return $ keepArg p
      , not <$> isUnboxCopattern (namedArg p)
      ]

compilePat :: DeBruijnPattern -> C (Hs.Pat ())
compilePat p@(VarP o _)
  | PatOWild <- patOrigin o = return $ Hs.PWildCard ()
  | otherwise               = Hs.PVar () . hsName <$> showTCM p
compilePat (ConP h i ps)
  | Just semantics <- isSpecialPat (conName h) = setCurrentRange h $ semantics h i ps
compilePat (ConP h _ ps) = do
  ps <- compilePats ps
  c <- hsQName (conName h)
  return $ pApp c ps
-- TODO: LitP
compilePat (ProjP _ q) = do
  reportSDoc "agda2hs.compile" 6 $ text "compiling copattern: " <+> text (prettyShow q)
  unlessM (asks isCompilingInstance) $
    genericDocError =<< text "not supported in Haskell: copatterns"
  let x = hsName $ prettyShow q
  return $ Hs.PVar () x
compilePat p = genericDocError =<< text "bad pattern:" <?> prettyTCM p

-- Local (where) declarations ---------------------------------------------

-- | Before checking a function, grab all of its local declarations.
-- TODO: simplify this when Agda exposes where-provenance in 'Internal' syntax
withFunctionLocals :: QName -> C a -> C a
withFunctionLocals q k = do
  ls <- takeWhile (isAnonymousModuleName . qnameModule . fst)
      . dropWhile ((<= q) . fst)
      . sortDefs <$> liftTCM curDefs
  withLocals ls k

-- | Retain only those local declarations that belong to current clause's module.
zoomLocals :: ModuleName -> LocalDecls -> LocalDecls
zoomLocals mname = filter ((mname `isLeParentModuleOf`) . qnameModule . fst)

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
