module Agda2Hs.Compile.ClassInstance where

import Control.Monad ( filterM, unless, void, when )
import Control.Monad.Except ( catchError )
import Control.Monad.Reader ( asks, local )

import Data.Foldable ( toList )
import Data.List ( nub )
import Data.Maybe ( isJust, isNothing, mapMaybe )
import qualified Data.HashMap.Strict as HMap

import Agda.Compiler.Backend

import Agda.Syntax.Common hiding ( Ranged )
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern ( patternToTerm )
import Agda.Syntax.Common.Pretty ( prettyShow )

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Errors ( prettyError )
import Agda.TypeChecking.Substitute ( Apply(applyE), absApp )
import Agda.TypeChecking.Records
import Agda.TypeChecking.Telescope ( mustBePi )
import Agda.TypeChecking.Warnings ( warning )

import Agda.Utils.Lens
import Agda.Utils.Monad ( ifNotM, whenM )
import Agda.Utils.Impossible ( __IMPOSSIBLE__ )

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Function
import Agda2Hs.Compile.Name
import Agda2Hs.Compile.Term
import Agda2Hs.Compile.Type
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils

import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils
  ( pp, replaceName, unQual )

enableCopatterns :: C a -> C a
enableCopatterns = local $ \e -> e { copatternsEnabled = True }

disableCopatterns :: C a -> C a
disableCopatterns = local $ \e -> e { copatternsEnabled = False }


-- | Enable the appropriate extensions for a given Haskell deriving strategy.
enableStrategy :: Maybe (Hs.DerivStrategy ()) -> C ()
enableStrategy Nothing = return ()
enableStrategy (Just s) = do
  tellExtension Hs.DerivingStrategies
  case s of
    Hs.DerivStock ()    -> return () -- is included in GHC
    Hs.DerivAnyclass () -> tellExtension Hs.DeriveAnyClass -- since 7.10.1
    Hs.DerivNewtype ()  -> tellExtension Hs.GeneralizedNewtypeDeriving -- since 6.8.1.
    Hs.DerivVia () t    -> tellExtension Hs.DerivingVia -- since 8.6.1


compileInstance :: InstanceTarget -> Definition -> C (Hs.Decl ())

compileInstance (ToDerivation strategy) def@Defn{..} =
  setCurrentRangeQ defName $ do
    reportSDoc "agda2hs.compile.instance" 13 $
      text "compiling instance" <+> prettyTCM defName <+> text "to standalone deriving"
    tellExtension Hs.StandaloneDeriving
    enableStrategy strategy
    ir <- compileInstRule [] [] (unEl defType)
    return $ Hs.DerivDecl () strategy Nothing ir

compileInstance ToDefinition def@Defn{..} =
  enableCopatterns $ setCurrentRangeQ defName $ do
    reportSDoc "agda2hs.compile.instance" 13 $
      text "compiling instance" <+> prettyTCM defName <+> text "to instance definition"
    ir <- compileInstRule [] [] (unEl defType)
    withFunctionLocals defName $ do
      reportSDoc "agda2hs.compile.instance" 20 $ vcat $
        text "compileInstance clauses: " :
        map (nest 2 . prettyTCM) funClauses
      let mod = qnameModule defName
      reportSDoc "agda2hs.compile.instance" 25 $ text "compileInstance module: " <+> prettyTCM mod
      tel <- lookupSection mod
      addContext tel $ do
        liftTCM $ setModuleCheckpointForInstanceChecking mod
        -- We intentionally do not apply getContextArgs eagerly here so dotted
        -- patterns corresponding to module parameters are correctly detected
        -- (see #306)
        (ds, rs) <- concatUnzip
                <$> mapM (\c -> withClauseLocals c $ compileInstanceClause mod defType c) funClauses
        reportSDoc "agda2hs.compile.instance" 20 $ vcat $
          text "compileInstance compiled clauses: " :
          map (nest 2 . text . pp) ds
        when (length (nub rs) > 1) $
          agda2hsErrorM $ fsep (pwords "More than one minimal record used.")
        return $ Hs.InstDecl () Nothing ir (Just ds)
    where Function{..} = theDef


-- | Check a @COMPILE AGDA2HS <instance> to <target>@ pragma: the target must be
-- an instance whose compiled Haskell declaration matches that of the source
-- instance. Comparing the compiled declarations means that the source instance
-- must be written in the same way as the target, including the names of any
-- local @where@ definitions.
--
-- The check is best-effort: if the two instances cannot be shown to match, a
-- warning is emitted instead of an error, since the target instance is the one
-- that is used in the generated code.
checkCompileToInstancePragma :: Definition -> String -> C ()
checkCompileToInstancePragma def s = noCheckNames $ noWriteExports $ do
  r <- resolveStringName s
  -- Start by adding the compile-to rule, so that the instance of `def` is
  -- compiled to the instance of `r` even if the check below fails.
  addCompileToName (defName def) r
  let header =
        [ "The instance" <+> prettyTCM (defName def) <+> "is annotated with a"
            <+> "`to` pragma targeting" <+> (prettyTCM r <> text ",") ]
      warn docs = warning =<< (CustomBackendWarning "agda2hs" <$> vcat (header ++ docs))
      unchecked reason = warn
        [ nest 2 $ "but its consistency could not be checked:" <+> reason ]
  -- An instance without a definition cannot be checked.
  case theDef def of
    Axiom{} -> unchecked "it is postulated"
    _       -> do
      rdef <- getConstInfo r
      if not (isJust $ defInstance rdef)
        then unchecked "the target is not an instance"
        else
          -- Compare the compiled instances. The target is compiled in the
          -- context of the module where it is defined, so that its local
          -- definitions are available. Neither instance is written to the
          -- current module, so no imports are recorded for them either.
          catchError
            (do d  <- noWriteImports $ compileInstance ToDefinition def
                rd <- withModuleOf r $ noWriteImports $ compileInstance ToDefinition rdef
                reportSDoc "agda2hs.compileto" 20 $ vcat
                  [ text "compiled source instance:" <+> text (pp d)
                  , text "compiled target instance:" <+> text (pp rd)
                  ]
                unless (d == rd) $ warn $
                  [ nest 2 "but the two instances do not compile to the same Haskell declaration:" ] ++
                  concat
                    [ ((text "compiled instance" <+> prettyTCM q) <> text ":") :
                      map (nest 2 . text) (lines $ pp x)
                    | (q, x) <- [(defName def, d), (r, rd)]
                    ])
            (\e -> do
              msg <- prettyError e
              unchecked $ vcat [ "the instances could not be compiled:", nest 2 (pure msg) ])


compileInstRule :: [Hs.TyVarBind ()] -> [Hs.Asst ()] -> Term -> C (Hs.InstRule ())
compileInstRule xs cs ty = do
  reportSDoc "agda2hs.compile.instance" 20 $ text "compileInstRule" <+> prettyTCM ty
  case unSpine1 ty of
    Def f es | Just args <- allApplyElims es -> do
      fty <- defType <$> getConstInfo f
      vs <- compileTypeArgs fty args
      f <- compileQName f
      return $
        Hs.IRule () (Just xs) (ctx cs) $ foldl (Hs.IHApp ()) (Hs.IHCon () f) (map pars vs)
      where ctx [] = Nothing
            ctx cs = Just (Hs.CxTuple () cs)
            -- put parens around anything except a var or a constant
            pars :: Hs.Type () -> Hs.Type ()
            pars t@(Hs.TyVar () _) = t
            pars t@(Hs.TyCon () _) = t
            pars t = Hs.TyParen () t
    Pi a b -> compileDomType (absName b) a >>= \case
      DomDropped -> underAbstr a b skip
      DomConstraint hsA ->
        underAbstraction a b (compileInstRule xs (cs ++ [hsA]) . unEl)
      DomType _ t -> __IMPOSSIBLE__
      DomForall Nothing -> underAbstr a b skip
      DomForall (Just x) ->
        underAbstraction a b (compileInstRule (xs ++ [x]) cs . unEl)
      where skip = compileInstRule xs cs . unEl
    _ -> __IMPOSSIBLE__


-- Plan:
--  - ✓ Eta-expand if no copatterns (top-level)
--  - ✓ drop default implementations and chase definitions of primitive methods in minimal records + *checks*
--  - ✓ compileInstanceClause on resulting clauses
--
-- *checks*
--  - ✓ Only one minimal record
--  - ✓ all primitives of the minimal are projected from the same dictionary
--  - ✓ default implementation that get dropped are also projected from that same dictionary


etaExpandClause :: Clause -> C [Clause]
etaExpandClause cl@Clause{clauseBody = Nothing} =
  agda2hsError "Instance definition with absurd pattern!"
etaExpandClause cl@Clause{namedClausePats = ps, clauseBody = Just t} = do
  case t of
    Con c _ _ -> do
      let fields = conFields c
      let cls = [ cl{ namedClausePats = ps ++ [unnamed . ProjP ProjSystem <$> f],
                      clauseBody      = Just $ t `applyE` [Proj ProjSystem $ unArg f] }
                | f <- fields ]
      return cls
    _ -> agda2hsErrorM $ fsep (pwords $
      "Type class instances must be defined using copatterns (or top-level" ++
      " records) and cannot be defined using helper functions.")


compileInstanceClause :: ModuleName -> Type -> Clause -> C ([Hs.InstDecl ()], [QName])
compileInstanceClause curModule ty c = ifNotM (keepClause c) (return ([], [])) $ do

  let naps = namedClausePats c

  -- there are no projection patterns: we need to eta-expand the clause
  if all (isNothing . isProjP) naps then do
    cs <- etaExpandClause c
    reportSDoc "agda2hs.compile.instance" 20 $ vcat $
      text "compileInstance expanded clauses: " :
      map (nest 2 . prettyTCM) cs
    concatUnzip <$> mapM (compileInstanceClause curModule ty) cs

  -- otherwise we seek the first projection pattern
  else addContext (KeepNames $ clauseTel c) $ do
    checkForcedPatterns ty naps
    compileInstanceClause' curModule ty naps c { clauseTel = EmptyTel }

-- abuse compileClause:
-- 1. drop any patterns before record projection to suppress the instance arg
-- 2. use record proj. as function name
-- 3. process remaining patterns as usual
compileInstanceClause' :: ModuleName -> Type -> NAPs -> Clause -> C ([Hs.InstDecl ()], [QName])
compileInstanceClause' curModule ty [] c = __IMPOSSIBLE__
compileInstanceClause' curModule ty (p:ps) c

  -- reached record projection
  | ProjP _ q <- namedArg p = do

    -- we put back the remaining patterns in the original clause
    let c' = c {namedClausePats = ps}

    -- We want the actual field name, not the instance-opened projection.
    (q, _, _) <- origProjection q
    arg <- fieldArgInfo q


    reportSDoc "agda2hs.compile.instance" 15 $
      text "Compiling instance clause for" <+> prettyTCM (Arg arg $ Def q [])

    reportSDoc "agda2hs.compile.instance" 15 $
      text "Instance type: " <+> prettyTCM ty

    -- retrieve the type of the projection
    Just (unEl -> Pi a b) <- getDefType q ty
    -- We don't really have the information available to reconstruct the instance
    -- head. However, all dependencies on the instance head are in erased positions,
    -- so we can just use a dummy term instead
    let instanceHead = __DUMMY_TERM__
        ty' = b `absApp` instanceHead

    reportSDoc "agda2hs.compile.instance" 15 $
      text "Clause type: " <+> prettyTCM ty'

    reportSDoc "agda2hs.compile.instance" 15 $
      text "Clause patterns:" <+> prettyTCM (namedArg <$> ps)

    reportSDoc "agda2hs.compile.instance" 18 $ text "Current module:" <+> prettyTCM curModule
    ls <- asks locals
    reportSDoc "agda2hs.compile.instance" 18 $ text "Clause locals:" <+> prettyTCM ls

    let uf = compileName (qnameName q)

    -- Register the method in the import list (e.g. Default(def)) when it is a
    -- field of a record that is compiled to a Haskell type class.
    let registerMethodImport = whenM (isClassFunction q) $ void (compileQName q)

    let
      (.~) :: QName -> QName -> Bool
      x .~ y = nameConcrete (qnameName x) == nameConcrete (qnameName y)

      -- Whether two names live in records of the same parent module. This is
      -- used to tell a field of a superclass or minimal record apart from an
      -- unrelated definition that happens to have the same concrete name, such
      -- as a renamed builtin.
      sameParentModule :: QName -> QName -> Bool
      sameParentModule x y =
        init (mnameToList $ qnameModule x) == init (mnameToList $ qnameModule y)

    if
      -- Instance field: check canonicity.
      | isInstance arg -> do
          unless (null ps) $ agda2hsError "not allowed: explicitly giving superclass"
          body <- case clauseBody c' of
            Nothing -> agda2hsError "not allowed: absurd clause for superclass"
            Just b  -> return b
          addContext (clauseTel c) $ do
            liftTCM $ setModuleCheckpointForInstanceChecking curModule
            checkInstance body
          reportSDoc "agda2hs.compile.instance" 20 $ vcat
            [ text "compileInstanceClause dropping clause"
            , nest 2 $ prettyTCM c
            ]
          return ([], [])

      -- Projection of a primitive field: chase down definition and inline as instance clause.
      | Clause {namedClausePats = [], clauseBody = Just (Def n es)} <- c'
      , [(_, f)] <- mapMaybe isProjElim es
      , f .~ q -> do
        reportSDoc "agda2hs.compile.instance" 20 $
          text "Instance clause is projected from" <+> prettyTCM (Def n [])
        reportSDoc "agda2hs.compile.instance" 40 $
          text $ "raw name: " ++ prettyShow (Def n [])
        d@Defn{..} <- getConstInfo n
        let isExtLam = isExtendedLambdaName defName
            mod = if isExtLam then curModule else qnameModule defName
            -- The clauses of a pattern lambda in the right-hand side of the
            -- instance clause see the where block of that clause.
            inheritWhere cl
              | isExtLam  = cl { clauseWhereModule = clauseWhereModule c }
              | otherwise = cl
        let isMatchingProj [] = False
            isMatchingProj (p:ps) | ProjP _ g <- namedArg p = g .~ q
            isMatchingProj (p:ps) = isMatchingProj ps
        (fc, rs) <- withCurrentModule mod
            $ fmap concatUnzip
            . mapM (compileInstanceClause mod defType . inheritWhere)
            . filter (isMatchingProj . namedClausePats)
            $ funClauses theDef
        let hd = compileName (qnameName defName)
        let fc' = {- dropPatterns 1 $ -} replaceName hd uf fc
        when (not (null fc')) registerMethodImport
        reportSDoc "agda2hs.compile.instance" 6 $ vcat $
          text "compileInstanceClause compiled clause: " :
          map (nest 2 . text . pp) fc'
        return (fc', n:rs)

       -- Projection of a default implementation: drop while making sure these are drawn from the
       -- same (minimal) dictionary as the primitive fields.
      | Clause {namedClausePats = [], clauseBody = Just (Def n es)} <- c'
      , n .~ q
      , sameParentModule n q -> do
        let err = agda2hsError $ "illegal instance declaration: instances using default methods should use a named definition or an anonymous `λ where`."
            filterArgs :: Type -> [Term] -> C [Term]
            filterArgs ty [] = return []
            filterArgs ty (v:vs) = do
              reportSDoc "agda2hs.compile.instance" 25 $ text "filterArgs: v =" <+> prettyTCM v
              (a,b) <- mustBePi ty
              reportSDoc "agda2hs.compile.instance" 25 $ text "filterArgs: a =" <+> prettyTCM a
              let rest = underAbstraction a b $ \b' -> filterArgs b' vs
              compileDom a >>= \case
                DODropped -> rest
                DOType -> rest
                DOTerm -> (v:) <$> rest
                DOInstance -> err
        ty <- defType <$> getConstInfo n
        traverse (filterArgs ty) (map unArg <$> allApplyElims es) >>= \case
          Just [ Def f _ ] -> do
            reportSDoc "agda2hs.compile.instance" 20 $ vcat
                [ text "Dropping default instance clause" <+> prettyTCM c'
                , text "with minimal dictionary" <+> prettyTCM f
                ]
            reportSDoc "agda2hs.compile.instance" 40 $
                text $ "raw dictionary:" ++ prettyShow f
            return ([], [f])
          _ -> err

      -- No minimal dictionary used, proceed with compiling as a regular clause.
      | otherwise -> do
        registerMethodImport
        reportSDoc "agda2hs.compile.instance" 20 $ text "Compiling instance clause" <+> prettyTCM c'
        ms <- disableCopatterns $ compileClause curModule [] Nothing uf ty' c'
        let cc = Hs.FunBind () (toList ms)
        reportSDoc "agda2hs.compile.instance" 20 $ vcat
          [ text "compileInstanceClause compiled clause"
          , nest 2 $ text $ pp cc
          ]
        return ([Hs.InsDecl () cc], [])

-- finding a pattern other than a projection: we skip
-- NOTE(flupe): actually I think we may want to throw hard errors here
--              if there is something other than erased parameters
compileInstanceClause' curModule ty (p:ps) c = do
  (a, b) <- mustBePi ty
  compileInstanceClause' curModule (absApp b (patternToTerm $ namedArg p)) ps c

fieldArgInfo :: QName -> C ArgInfo
fieldArgInfo f = do
  r <- maybe badness return =<< liftTCM (getRecordOfField f)
  Record{ recFields = fs } <- theDef <$> getConstInfo r
  case filter ((== f) . unDom) fs of
    df : _ -> return $ getArgInfo df
    []     -> badness
  where
    badness = agda2hsErrorM $ text "Not a record field:" <+> prettyTCM f


findDefinitions :: (QName -> Definition -> C Bool) -> ModuleName -> C [Definition]
findDefinitions p m = do
  localDefs    <- (^. sigDefinitions) . (^. stSignature) <$> getTCState
  importedDefs <- (^. sigDefinitions) . (^. stImports)   <$> getTCState
  let allDefs = HMap.union localDefs importedDefs
      inMod = [ (x, def) | (x, def) <- HMap.toList allDefs, isInModule x m ]
  map snd <$> filterM (uncurry p) inMod

lookupDefaultImplementations :: QName -> [Hs.Name ()] -> C [Definition]
lookupDefaultImplementations recName fields = do
  let modName = qnameToMName recName
      isField f _ = pure $ compileName (qnameName f) `elem` fields
  findDefinitions isField modName

classMemberNames :: Definition -> C [Hs.Name ()]
classMemberNames def =
  case theDef def of
    Record{recFields = fs} -> fmap unQual <$> traverse compileQName (map unDom fs)
    _ -> agda2hsErrorM $ text "Not a record:" <+> prettyTCM (defName def)
