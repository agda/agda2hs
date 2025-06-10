module Agda2Hs.Compile.Term where

import Control.Arrow ( (>>>), (&&&), second )
import Control.Monad ( zipWithM )
import Control.Monad.Except
import Control.Monad.Reader

import Data.Foldable ( toList )
import Data.Functor ( ($>) )
import Data.List ( isPrefixOf )
import Data.Maybe ( fromMaybe, isJust )
import qualified Data.Text as Text ( unpack )
import qualified Data.Set as Set ( singleton )

import Agda.Syntax.Common.Pretty ( prettyShow )
import qualified Agda.Syntax.Common.Pretty as P
import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Internal

import Agda.TypeChecking.CheckInternal ( infer )
import Agda.TypeChecking.Constraints ( noConstraints )
import Agda.TypeChecking.Conversion ( equalTerm )
import Agda.TypeChecking.InstanceArguments ( findInstance )
import Agda.TypeChecking.MetaVars ( newInstanceMeta )
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records ( shouldBeProjectible, isRecordType, recordFieldNames )
import Agda.TypeChecking.Datatypes ( getConType )
import Agda.TypeChecking.Reduce ( unfoldDefinitionStep, instantiate, reduce )
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope ( telView, mustBePi, piApplyM, flattenTel )
import Agda.TypeChecking.ProjectionLike ( reduceProjectionLike )

import Agda.Utils.Lens
import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Size

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name ( compileQName, importInstance )

import Agda2Hs.Compile.Type ( compileType, compileDom, DomOutput(..), compileTelSize )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.Compile.Var ( compileDBVar )

import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils
  ( hsName, pp, eApp, hsLambda, hsUnqualName, hsVar )

import {-# SOURCE #-} Agda2Hs.Compile.Function ( compileClause' )
import qualified Data.List as L


-- * Compilation of special definitions

type DefCompileRule = Type -> [Term] -> C (Hs.Exp ())

isSpecialDef :: QName -> Maybe DefCompileRule
isSpecialDef q = case prettyShow q of
  _ | isExtendedLambdaName q     -> Just (lambdaCase q)
  "Haskell.Prim.if_then_else_"   -> Just ifThenElse
  "Haskell.Prim.case_of_"        -> Just caseOf
  "Haskell.Prim.the"             -> Just expTypeSig
  "Haskell.Extra.Delay.runDelay" -> Just compileErasedApp
  "Agda.Builtin.Word.primWord64FromNat" -> Just primWord64FromNat
  _                              -> Nothing


-- | Compile a @\where@ to the equivalent @\case@ expression.
lambdaCase :: QName -> DefCompileRule
lambdaCase q ty args = compileLocal $ setCurrentRangeQ q $ do
  Function
    { funClauses = cls
    , funExtLam  = Just ExtLamInfo {extLamModule = mname}
    } <- theDef <$> getConstInfo q

  npars <- size <$> lookupSection mname

  let (pars, rest) = splitAt npars args
      cs           = applys cls pars

  ty' <- piApplyM ty pars

  cs <- mapMaybeM (compileClause' mname (Just q) (hsName "(lambdaCase)") ty') cs

  case cs of
    -- If there is a single clause and all proper patterns got erased,
    -- we turn the remaining arguments into normal lambdas.
    [Hs.Match _ _ ps (Hs.UnGuardedRhs _ rhs) _]
      | null ps -> return rhs
      | all isVarPat ps -> return $ Hs.Lambda () ps rhs
    _ -> do
      lcase <- hsLCase =<< mapM clauseToAlt cs -- Pattern lambdas cannot have where blocks
      eApp lcase <$> compileArgs ty' rest
      -- undefined -- compileApp lcase (undefined, undefined, rest)

  where
    isVarPat :: Hs.Pat () -> Bool
    isVarPat Hs.PVar{} = True
    isVarPat _ = False

-- | Compile @if_then_else_@ to a Haskell @if ... then ... else ... @ expression.
ifThenElse :: DefCompileRule
ifThenElse ty args = compileArgs ty args >>= \case
  -- fully applied
  b : t : f : es' -> return $ Hs.If () b t f `eApp` es'
  -- partially applied
  _               -> agda2hsError "if_then_else_ must be fully applied"


-- | Compile @case_of_@ to Haskell @\case@ expression.
caseOf :: DefCompileRule
caseOf ty args = compileArgs ty args >>= \case
  -- applied to pattern lambda (that we remove, hence decrementLCase)
  e : Hs.LCase _ alts : es' -> decrementLCase $> eApp (Hs.Case () e alts) es'
  -- applied to regular lambda
  e : Hs.Lambda _ (p : ps) b : es' ->
    let lam [] = id
        lam qs = Hs.Lambda () qs
    in return $ eApp (Hs.Case () e [Hs.Alt () p (Hs.UnGuardedRhs () $ lam ps b) Nothing]) es'
  _ -> agda2hsError "case_of_ must be fully applied to a lambda term"


-- | Compile @the@ to an explicitly-annotated Haskell expression.
expTypeSig :: DefCompileRule
expTypeSig ty args@(_:typ:_:_) = do
    annot    <- compileType typ
    exp:args <- compileArgs ty args
    pure (Hs.ExpTypeSig () exp annot `eApp` args)
expTypeSig _ _ = agda2hsError "`the` must be fully applied"

primWord64FromNat :: DefCompileRule
primWord64FromNat ty args = compileArgs ty args >>= \case
  -- literal
  n@Hs.Lit{} : _ -> return n
  -- anything else
  _ -> agda2hsError "primWord64FromNat must be applied to a literal"


compileVar :: Int -> Type -> [Term] -> C (Hs.Exp ())
compileVar i ty es = do
  reportSDoc "agda2hs.compile.term" 15 $ text "Reached variable"
  name <- compileDBVar i
  compileApp (hsVar name) ty es

-- | Compile constructors, defs and vars by
-- carefully moving projections out of elims and calling compileProj.
compileSpined
      :: ([Term] -> C (Hs.Exp ()))  -- Compilation continuation
      -> (Elims -> Term)            -- Term begin constructed
      -> Type                       -- Type of term
      -> Elims                      -- Elims the term is applied to
      -> C (Hs.Exp ())
compileSpined c tm ty [] = c []
compileSpined c tm ty (e@(Proj o q):es) = do
  let t = tm []
  ty' <- shouldBeProjectible t ty o q
  compileSpined (compileProj q ty t ty') (tm . (e:)) ty' es
compileSpined c tm ty (e@(Apply (unArg -> x)):es) = do
  (a, b) <- mustBePi ty
  compileSpined (c . (x:)) (tm . (e:)) (absApp b x) es
compileSpined _ _ _ _ = __IMPOSSIBLE__

-- | Compile a definition.
compileDef :: QName -> Type -> [Term] -> C (Hs.Exp ())
compileDef f ty args | Just sem <- isSpecialDef f = do
  reportSDoc "agda2hs.compile.term" 12 $ text "Compiling application of special function"
  sem ty args

compileDef f ty args =
  ifM (isTransparentFunction f) (compileErasedApp ty args) $
  ifM (isInlinedFunction f) (compileInlineFunctionApp f ty args) $ do
    reportSDoc "agda2hs.compile.term" 12 $ text "Compiling application of regular function:" <+> prettyTCM f

    let defMod = qnameModule f

    minRecord <- asks minRecordName
    -- TODO: simplify this when Agda exposes where-provenance in 'Internal' syntax
    outerWhereModules <- asks whereModules

    (ty', args') <-

      -- if the function comes from a where-clause
      -- or is a class-method for the class we are currently defining,
      -- we drop the module parameters
      if defMod `elem` outerWhereModules || Just defMod == minRecord then do
        npars <- size <$> lookupSection defMod
        let (pars, rest) = splitAt npars args
        ty' <- piApplyM ty pars
        pure (ty', rest)
      else pure (ty, args)

    reportSDoc "agda2hs.compile.term" 15 $ text "module args" <+> prettyTCM ty'
    reportSDoc "agda2hs.compile.term" 15 $ text "args to def: " <+> prettyTCM args'

    hsName <- compileQName f

    compileApp (Hs.Var () hsName) ty' args'


-- * Compilation of projection(-like) definitions

type ProjCompileRule = Type -> Term -> Type -> [Term] -> C (Hs.Exp ())


isSpecialProj :: QName -> Maybe ProjCompileRule
isSpecialProj q = case prettyShow q of
  "Agda.Builtin.FromNat.Number.fromNat"         -> Just fromNat
  "Haskell.Prim.Enum.Enum.enumFrom"             -> Just mkEnumFrom
  "Haskell.Prim.Enum.Enum.enumFromTo"           -> Just mkEnumFromTo
  "Haskell.Prim.Enum.Enum.enumFromThen"         -> Just mkEnumFromThen
  "Haskell.Prim.Enum.Enum.enumFromThenTo"       -> Just mkEnumFromThenTo
  "Haskell.Prim.Monad.Do.Monad._>>=_"           -> Just monadBind
  "Haskell.Prim.Monad.Do.Monad._>>_"            -> Just monadSeq
  "Agda.Builtin.FromNeg.Negative.fromNeg"       -> Just fromNeg
  "Agda.Builtin.FromString.IsString.fromString" -> Just fromString
  _                                             -> Nothing


compileClassFun :: QName -> ProjCompileRule
compileClassFun q _ w ty args = do
  hf     <- compileQName q
  curMod <- currentModule
  unless (curMod `isLeChildModuleOf` qnameModule q) $ checkInstance w
  eApp (Hs.Var () hf) <$> compileArgs ty args

compileTupleProjection :: QName -> Hs.Boxed -> ProjCompileRule
compileTupleProjection f b wty w ty args = do
  -- TODO: avoid redoing all of this work each time
  -- by storing the fields of each tuple type somewhere
  when (b == Hs.Unboxed) $ agda2hsError "projecting from unboxed tuples is not allowed"
  reportSDoc "agda2hs.term.proj" 12 $ text "compiling tuple projection"
  (r, pars, def) <- lift $ fromMaybe __IMPOSSIBLE__ <$> isRecordType wty
  let fields = map unDom $ _recFields def
      fieldTypes = flattenTel $ _recTel def `apply` pars
  fname <- compileTupleFields fields fieldTypes >>= \case
    [f1,f2] | f == f1 -> return $ hsName "fst"
            | f == f2 -> return $ hsName "snd"
            | otherwise -> __IMPOSSIBLE__
    fs' -> agda2hsStringError $
      "cannot project from tuple with " ++ show (size fs') ++ " fields"
  cw <- compileTerm wty w
  cargs <- compileArgs ty args
  return $ eApp (Hs.Var () $ Hs.UnQual () fname) (cw:cargs)

  where
    compileTupleFields :: [QName] -> [Dom Type] -> C [QName]
    compileTupleFields fs tys = catMaybes <$> zipWithM compileTupleField fs tys

    compileTupleField :: QName -> Dom Type -> C (Maybe QName)
    compileTupleField f ty = compileDom ty >>= \case
      DODropped -> return Nothing
      DOTerm -> return (Just f)
      DOType -> agda2hsErrorM $ "illegal type field in tuple record:" <+> prettyTCM f
      DOInstance -> agda2hsErrorM $ "illegal instance field in tuple record:" <+> prettyTCM f


-- | Compile a projection(-like) definition
compileProj
  :: QName  -- ^ Name of the projection
  -> Type   -- ^ Type of the term the projection is being applied to
  -> Term   -- ^ Term the projection is being applied to
  -> Type   -- ^ Return type of the projection
  -> [Term] -- ^ Arguments the projection of the term is applied to
  -> C (Hs.Exp ())
compileProj q tty t ty args | Just rule <- isSpecialProj q = rule tty t ty args
compileProj q tty t ty args =
  -- unboxed projection: we drop the projection
  ifM (isJust <$> isUnboxProjection q) (eApp <$> compileTerm tty t <*> compileArgs ty args) $
  -- class projection: we check the instance and drop it
  ifM (isClassFunction q) (compileClassFun q tty t ty args) $
  ifJustM (isTupleProjection q) (\b -> compileTupleProjection q b tty t ty args) $
  do
  -- NOTE(flupe): maybe we want Dom Type for the record arg
    name <- compileQName q
    arg  <- compileTerm tty t
    compileApp (Hs.Var () name `eApp` [arg]) ty args

-- | Utility for translating class methods to special Haskell counterpart.
-- This runs an instance check.
specialClassFunction :: ([Hs.Exp ()] -> Hs.Exp ()) -> ProjCompileRule
specialClassFunction f = specialClassFunctionM (pure . f)

specialClassFunctionM :: ([Hs.Exp ()] -> C (Hs.Exp ())) -> ProjCompileRule
specialClassFunctionM f _ w ty args = checkInstance w >> (f =<< compileArgs ty args)

specialClassFunction1 :: Hs.Exp () -> (Hs.Exp () -> Hs.Exp ()) -> ProjCompileRule
specialClassFunction1 v f = specialClassFunction $ \case
  (a : es) -> f a `eApp` es
  []       -> v

specialClassFunction2 :: Hs.Exp () -> (Hs.Exp () -> Hs.Exp () -> Hs.Exp ()) -> ProjCompileRule
specialClassFunction2 v f = specialClassFunction $ \case
  (a : b : es) -> f a b `eApp` es
  es           -> v `eApp` es

specialClassFunction3 :: Hs.Exp () -> (Hs.Exp () -> Hs.Exp () -> Hs.Exp () -> Hs.Exp ()) -> ProjCompileRule
specialClassFunction3 v f = specialClassFunction $ \case
  (a : b : c : es) -> f a b c `eApp` es
  es               -> v `eApp` es

-- Note: currently the second (instance) argument {{_ : Constraint n}}
-- is compiled and then dropped here, ideally it would not be compiled
-- at all.
fromNat :: ProjCompileRule
fromNat = specialClassFunction2 (hsVar "fromIntegral") $ \v _ -> case v of
  n@Hs.Lit{} -> n
  v          -> hsVar "fromIntegral" `eApp` [v]

mkEnumFrom :: ProjCompileRule
mkEnumFrom = specialClassFunction1 (hsVar "enumFrom") $ Hs.EnumFrom ()

mkEnumFromTo :: ProjCompileRule
mkEnumFromTo = specialClassFunction2 (hsVar "enumFromTo") $ Hs.EnumFromTo ()

mkEnumFromThen :: ProjCompileRule
mkEnumFromThen = specialClassFunction2 (hsVar "enumFromThen") $ Hs.EnumFromThen ()

mkEnumFromThenTo :: ProjCompileRule
mkEnumFromThenTo = specialClassFunction3 (hsVar "enumFromThenTo") $ Hs.EnumFromThenTo ()

-- Same comment as for fromNat
fromNeg :: ProjCompileRule
fromNeg = specialClassFunction2 negFromIntegral $ \v _ -> case v of
  n@Hs.Lit{} -> Hs.NegApp () n
  v          -> negFromIntegral `eApp` [v]
  where
    negFromIntegral = hsVar "negate" `o` hsVar "fromIntegral"
    -- TODO: move this to HsUtils
    f `o` g = Hs.InfixApp () f (Hs.QVarOp () $ hsUnqualName "_._") g

-- Same comment as for fromNat
fromString :: ProjCompileRule
fromString = specialClassFunction2 (hsVar "fromString") $ \v _ -> case v of
  s@Hs.Lit{} -> s
  v          -> hsVar "fromString" `eApp` [v]

-- | Compile monadic bind operator _>>=_ to Haskell do notation.
monadBind :: ProjCompileRule
monadBind = specialClassFunctionM $ \case
  [u, Hs.Lambda _ [p] v] -> pure $ bind' u p v
  [u, Hs.LCase () [Hs.Alt () p (Hs.UnGuardedRhs () v) Nothing]] ->
    decrementLCase >> return (bind' u p v)
  vs -> pure $ hsVar "_>>=_" `eApp` vs
  where
    bind' :: Hs.Exp () -> Hs.Pat () -> Hs.Exp () -> Hs.Exp ()
    bind' u p v =
      let stmt1 = Hs.Generator () p u in
      case v of
        Hs.Do _ stmts -> Hs.Do () (stmt1 : stmts)
        _             -> Hs.Do () [stmt1, Hs.Qualifier () v]

-- | Compile monadic bind operator _>>_ to Haskell do notation.
monadSeq :: ProjCompileRule-- TElims -> C (Hs.Exp ())
monadSeq = specialClassFunction $ \case
  (u : v : vs) -> do
    let stmt1 = Hs.Qualifier () u
    case v of
      Hs.Do _ stmts -> Hs.Do () (stmt1 : stmts)
      _             -> Hs.Do () [stmt1, Hs.Qualifier () v]
  vs -> hsVar "_>>_" `eApp` vs


-- * Compilation of constructors

type ConCompileRule = Type -> [Term] -> C (Hs.Exp ())

-- | Custom compilation rules for special constructors.
isSpecialCon :: QName -> Maybe ConCompileRule
isSpecialCon = prettyShow >>> \case
  "Haskell.Prim.Tuple._,_"          -> Just tupleTerm
  "Haskell.Prim.Tuple._×_×_._,_,_"  -> Just tupleTerm
  "Haskell.Prim.Int.Int.int64"      -> Just int64Term
  "Haskell.Extra.Sigma._,_"         -> Just tupleTerm
  "Haskell.Extra.Erase.Erased"      -> Just erasedTerm
  "Haskell.Extra.Delay.Delay.now"   -> Just compileErasedApp
  "Haskell.Extra.Delay.Delay.later" -> Just compileErasedApp
  _                                 -> Nothing

tupleTerm :: ConCompileRule
tupleTerm = compileApp' (Hs.Tuple () Hs.Boxed)

erasedTerm :: ConCompileRule
erasedTerm _ _ = pure (Hs.Tuple () Hs.Boxed [])

int64Term :: ConCompileRule
int64Term ty args = compileArgs ty args >>= \case
  n@Hs.Lit{} : _ -> return n
  _ -> agda2hsError "int64 must be applied to a literal"

-- | @compileErasedApp@ compiles the application of unboxed constructors
-- and transparent functions.
-- Precondition: at most one argument is preserved.
compileErasedApp :: Type -> [Term] -> C (Hs.Exp ())
compileErasedApp ty args = do
  reportSDoc "agda2hs.compile.term" 12 $ text "Compiling application of transparent function or erased unboxed constructor"
  reportSDoc "agda2hs.compile.term" 12 $ text "Args" <+> prettyTCM args
  reportSDoc "agda2hs.compile.term" 12 $ text "Type" <+> prettyTCM ty
  compileArgs ty args >>= \case
    []  -> return $ hsVar "id"
    [v] -> return v
    _   -> __IMPOSSIBLE__


compileCon :: ConHead -> ConInfo -> Type -> [Term] -> C (Hs.Exp ())
compileCon h i ty args = do
  let c = conName h
  ifJust  (isSpecialCon c)       (\semantics -> semantics ty args) $ do
  ifJustM (isUnboxConstructor c) (\_ -> compileErasedApp ty args)  $ do
  ifJustM (isTupleConstructor c) (\b -> compileTuple ty b args)    $ do
    info <- getConstInfo c
    -- the constructor may be a copy introduced by module application,
    -- therefore we need to find the original constructor
    if defCopy info then
      let Constructor{conSrcCon = ch'} = theDef info in
      compileCon ch' i ty args
    else do
      con <- Hs.Con () <$> compileQName c
      compileApp con ty args

compileTuple :: Type -> Hs.Boxed -> [Term] -> C (Hs.Exp ())
compileTuple ty b args = do
  tellUnboxedTuples b
  (ty', vs) <- compileArgs' ty args
  TelV tel _ <- telView ty'
  missing <- compileTelSize tel
  let given = size vs
  if -- No arguments: return unit constructor () or (# #)
     | given == 0 && missing == 0 -> return $
         Hs.Con () $ Hs.Special () $ case b of
           Hs.Boxed -> Hs.UnitCon ()
           Hs.Unboxed -> Hs.UnboxedSingleCon ()
     -- All arguments missing: return tuple constructor
     -- e.g. (,) or (#,#)
     | given == 0 -> return $
         Hs.Con () $ Hs.Special () $ Hs.TupleCon () b missing
     -- All arguments given: return tuple
     -- e.g. (v1 , v2) or (# v1 , v2 #)
     | missing == 0 -> return $ Hs.Tuple () b vs
     -- Some arguments given, some missing: return tuple section
     -- e.g. (v1 ,) or (# v1, #)
     | otherwise -> do
         tellExtension $ Hs.TupleSections
         return $ Hs.TupleSection () b $
           map Just vs ++ replicate missing Nothing



-- * Term compilation

compileTerm :: Type -> Term -> C (Hs.Exp ())
compileTerm ty v = do

  reportSDoc "agda2hs.compile.term" 10  $ text "compiling term:" <+> prettyTCM v

  v <- instantiate v

  let bad s t = agda2hsErrorM $ vcat
        [ text "cannot compile" <+> text (s ++ ":")
        , nest 2 $ prettyTCM t
        ]

  reduceProjectionLike v >>= \case

    Def f es -> do
      ty <- defType <$> getConstInfo f
      compileSpined (compileDef f ty) (Def f) ty es

    Con ch ci es -> do
      Just ((_, _, _), ty) <- getConType ch ty
      compileSpined (compileCon ch ci ty) (Con ch ci) ty es

    Var i es     -> do
      ty <- typeOfBV i
      compileSpined (compileVar i ty) (Var i) ty es

    Lit l   -> compileLiteral l

    Lam v b -> compileLam ty v b

    v@Pi{} -> bad "function type" v
    v@Sort{} -> bad "sort type" v
    v@Level{} -> bad "level term" v
    v@MetaV{} -> bad "unsolved metavariable" v
    v@DontCare{} -> bad "irrelevant term" v
    v@Dummy{} -> bad "dummy term" v

-- | Check whether a domain is usable on the Haskell side.
--
-- That is the case if:
-- * it is usable on the Agda side (i.e neither erased nor irrelevant).
-- * is not of sort Prop.
usableDom :: Dom Type -> Bool
usableDom dom | Prop _ <- getSort dom = False
usableDom dom = usableModality dom


compileLam :: Type -> ArgInfo -> Abs Term -> C (Hs.Exp ())
compileLam ty argi abs = do
  reportSDoc "agda2hs.compile.term" 50 $ text "Reached lambda"
  (dom, cod) <- mustBePi ty

  -- unusable domain, we remove the lambda and compile the body only
  if not (usableDom dom) then
    addContext dom $ compileTerm (absBody cod) (absBody abs)

  -- usable domain, user-written lambda is preserved
  else if getOrigin argi == UserWritten then do

    when (patternInTeleName `isPrefixOf` absName abs) $ agda2hsError $
      "Record pattern translation not supported. Use a pattern matching lambda instead."

    reportSDoc "agda2hs.compile" 17 $ text "compiling regular lambda"

    let varName = absName abs
        ctxElt  = (varName,) <$> dom

    hsLambda varName <$> addContext ctxElt (compileTerm (absBody cod) (absBody abs))

  -- usable domain, generated lambda means we introduce a section
  else do

    let varName = absName abs
        ctxElt  = (varName,) <$> dom

    addContext ctxElt $ do
      x <- compileDBVar 0
      compileTerm (absBody cod) (absBody abs) <&> \case
        Hs.InfixApp () a op b | a == hsVar x ->
          if pp op == "-" then -- Jesper: no right section for minus, as Haskell parses this as negation!
            Hs.LeftSection () b (Hs.QConOp () $ Hs.UnQual () $ hsName "subtract")
          else
            Hs.RightSection () op b -- System-inserted visible lambdas can only come from sections
        body -> hsLambda x body


-- | Compile the application of a function definition marked as inlinable.
-- The provided arguments will get substituted in the function body, and the missing arguments
-- will get quantified with lambdas.
compileInlineFunctionApp :: QName -> Type -> [Term] -> C (Hs.Exp ())
compileInlineFunctionApp f ty args = do
  reportSDoc "agda2hs.compile.term" 12 $ text "Compiling application of inline function"

  def <- getConstInfo f

  let ty' = defType def
  let Function{funClauses = cs} = theDef def
  let [Clause{namedClausePats = pats}] = filter (isJust . clauseBody) cs

  ty'' <- piApplyM ty args
  -- NOTE(flupe): very flimsy, there has to be a better way
  etaExpand (drop (length args) pats) ty' args >>= compileTerm ty''

  where
    -- inline functions can only have transparent constructor patterns and variable patterns
    extractPatName :: DeBruijnPattern -> ArgName
    extractPatName (VarP _ v) = dbPatVarName v
    extractPatName (ConP _ _ args) =
      let arg = namedThing $ unArg $ maybe __IMPOSSIBLE__ fst $ L.uncons $ filter (usableModality `and2M` visible) args
      in extractPatName arg
    extractPatName _ = __IMPOSSIBLE__

    extractName :: NamedArg DeBruijnPattern -> ArgName
    extractName (unArg -> np)
      | Just n <- nameOf np = rangedThing (woThing n)
      | otherwise = extractPatName (namedThing np)

    etaExpand :: NAPs -> Type -> [Term] -> C Term
    etaExpand [] ty args = do
      r <- liftReduce
            $ locallyReduceDefs (OnlyReduceDefs $ Set.singleton f)
            $ unfoldDefinitionStep (Def f [] `applys` args) f (Apply . defaultArg <$> args)
      case r of
        YesReduction _ t -> pure t
        _ -> agda2hsErrorM $ text "Could not reduce inline function" <+> prettyTCM f

    etaExpand (p:ps) ty args = do
      (dom, cod) <- mustBePi ty
      let ai = domInfo dom
      Lam ai . mkAbs (extractName p) <$> etaExpand ps (absBody cod) (raise 1 args ++ [ var 0 ])


compileApp :: Hs.Exp () -> Type -> [Term] -> C (Hs.Exp ())
compileApp = compileApp' . eApp

compileApp' :: ([Hs.Exp ()] -> Hs.Exp ()) -> Type -> [Term] -> C (Hs.Exp ())
compileApp' acc ty args = acc <$> compileArgs ty args

-- | Compile a list of arguments applied to a function of the given type.
compileArgs :: Type -> [Term] -> C [Hs.Exp ()]
compileArgs ty args = snd <$> compileArgs' ty args

compileArgs' :: Type -> [Term] -> C (Type, [Hs.Exp ()])
compileArgs' ty [] = pure (ty, [])
compileArgs' ty (x:xs) = do
  (a, b) <- mustBePi ty
  let rest = compileArgs' (absApp b x) xs
  compileDom a >>= \case
    DODropped  -> rest
    DOInstance -> checkInstance x *> rest
    DOType     -> checkValidType x *> rest
    DOTerm     -> second . (:) <$> compileTerm (unDom a) x <*> rest

-- We check that type arguments compile to a valid Haskell type
-- before dropping them, see issue #357.
checkValidType :: Term -> C ()
checkValidType x = noWriteImports (compileType x) *> return ()

clauseToAlt :: Hs.Match () -> C (Hs.Alt ())
clauseToAlt (Hs.Match _ _ [p] rhs wh) = pure $ Hs.Alt () p rhs wh
clauseToAlt (Hs.Match _ _ ps _ _)     = agda2hsError "Pattern matching lambdas must take a single argument"
clauseToAlt Hs.InfixMatch{}           = __IMPOSSIBLE__

compileLiteral :: Literal -> C (Hs.Exp ())
compileLiteral (LitNat n)    = return $ Hs.intE n
compileLiteral (LitFloat d)  = return $ Hs.Lit () $ Hs.Frac () (toRational d) (show d)
compileLiteral (LitWord64 w) = return $ Hs.Lit () $ Hs.PrimWord () (fromIntegral w) (show w)
compileLiteral (LitChar c)   = return $ Hs.charE c
compileLiteral (LitString t) = return $ Hs.Lit () $ Hs.String () s s
  where s = Text.unpack t
compileLiteral l             = agda2hsErrorM $ text "bad term:" <?> prettyTCM (Lit l)


checkInstance :: Term -> C ()
checkInstance u = do
  reportSDoc "agda2hs.checkInstance" 12 $ text "checkInstance" <+> prettyTCM u
  reduce u >>= \case
    Var x es -> do
      unlessM (isInstance <$> domOfBV x) illegalInstance
      checkInstanceElims es
    Def f es -> do
      unlessM (isJust . defInstance <$> getConstInfo f) illegalInstance
      importInstance f
      checkInstanceElims es
  -- We need to compile applications of `fromNat`, `fromNeg`, and
  -- `fromString` where the constraint type is ⊤ or IsTrue .... Ideally
  -- this constraint would be marked as erased but this would involve
  -- changing Agda builtins.
    Con c _ _
      | prettyShow (conName c) == "Agda.Builtin.Unit.tt" ||
        prettyShow (conName c) == "Haskell.Prim.IsTrue.itsTrue" ||
        prettyShow (conName c) == "Haskell.Prim.IsFalse.itsFalse" -> return ()
    _ -> illegalInstance

  where
    illegalInstance :: C ()
    illegalInstance = do
      reportSDoc "agda2hs.checkInstance" 15 $ text "illegal instance: " <+> pretty u
      agda2hsErrorM $ text "illegal instance: " <+> prettyTCM u

    checkInstanceElims :: Elims -> C ()
    checkInstanceElims = mapM_ checkInstanceElim

    checkInstanceElim :: Elim -> C ()
    checkInstanceElim (Apply v) =
      when (isInstance v && usableQuantity v) $
        checkInstance $ unArg v
    checkInstanceElim IApply{} = illegalInstance
    checkInstanceElim (Proj _ f) =
      unlessM (isInstance . defArgInfo <$> getConstInfo f) illegalInstance
