module Agda2Hs.Compile.Term
  ( compileTerm
  ) where

import Control.Arrow ( (>>>), (&&&) )
import Control.Monad ( unless )
import Control.Monad.Reader

import Data.Foldable ( toList )
import Data.Functor ( ($>) )
import Data.List ( isPrefixOf )
import Data.Maybe ( fromMaybe, isJust )
import qualified Data.Text as Text ( unpack )
import qualified Data.Set as Set ( singleton )

import qualified Language.Haskell.Exts as Hs

import Agda.Syntax.Common.Pretty ( prettyShow )
import qualified Agda.Syntax.Common.Pretty as P
import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records ( shouldBeProjectible )
import Agda.TypeChecking.Datatypes ( getConType )
import Agda.TypeChecking.Reduce ( unfoldDefinitionStep, reduce )
import Agda.TypeChecking.Substitute ( Apply(applyE), applys, raise, mkAbs, theTel, absBody, absApp )
import Agda.TypeChecking.Telescope ( telView )

import Agda.Utils.Lens
import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Tuple ( mapSndM )

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name ( compileQName )

import Agda2Hs.Compile.Type ( compileType, compileDom, compiledDom, DomOutput(..) )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.Compile.Var ( compileDBVar )
import Agda2Hs.HsUtils

import {-# SOURCE #-} Agda2Hs.Compile.Function ( compileClause' )

-- | Typed Elims.
type TElims =
  ( Type          -- ^ type of the thing being applied.
  , Elims -> Term -- ^ thing being applied.
  , Elims         -- ^ elims being applied to.
  )

-- * Compilation of special definitions

isSpecialDef :: QName -> Maybe (TElims -> C (Hs.Exp ()))
isSpecialDef _ = Nothing

  {-
isSpecialDef q = case prettyShow q of
  -- _ | isExtendedLambdaName q                    -> Just $ lambdaCase q
  "Haskell.Prim.if_then_else_"                  -> Just ifThenElse
  "Haskell.Prim.case_of_"                       -> Just caseOf
  --"Haskell.Prim.the"                            -> Just expTypeSig
  "Haskell.Prim.Monad.Do.Monad._>>=_"           -> Just monadBind
  "Haskell.Prim.Monad.Do.Monad._>>_"            -> Just monadSeq
  "Haskell.Extra.Delay.runDelay"                -> Just compileErasedApp
  "Haskell.Prim.Enum.Enum.enumFrom"             -> Just mkEnumFrom
  "Haskell.Prim.Enum.Enum.enumFromTo"           -> Just mkEnumFromTo
  "Haskell.Prim.Enum.Enum.enumFromThen"         -> Just mkEnumFromThen
  "Haskell.Prim.Enum.Enum.enumFromThenTo"       -> Just mkEnumFromThenTo
  "Agda.Builtin.FromNat.Number.fromNat"         -> Just fromNat
  "Agda.Builtin.FromNeg.Negative.fromNeg"       -> Just fromNeg
  "Agda.Builtin.FromString.IsString.fromString" -> Just fromString
  _                                             -> Nothing
  -}


  {-
-- | Compile a lambda-case to the equivalent @\case@ expression.
lambdaCase :: QName -> TElims -> C (Hs.Exp ())
lambdaCase q tes = setCurrentRangeQ q $ do
  Function{funClauses = cls, funExtLam = Just ExtLamInfo {extLamModule = mname}}
    <- theDef <$> getConstInfo q
  npars <- size <$> lookupSection mname
  let (pars, rest) = splitAt npars tes
      cs           = applys cls (snd <$> pars)
  cs <- mapMaybeM (compileClause' (qnameModule q) $ hsName "(lambdaCase)") cs
  case cs of
    -- If there is a single clause and all patterns got erased, we
    -- simply return the body.
    [Hs.Match _ _ [] (Hs.UnGuardedRhs _ rhs) _] -> return rhs
    _ -> do
      lcase <- hsLCase =<< mapM clauseToAlt cs -- Pattern lambdas cannot have where blocks
      eApp lcase <$> compileElims rest

-- | Compile @if_then_else_@ to a Haskell @if ... then ... else ... @ expression.
ifThenElse :: TElims -> C (Hs.Exp ())
ifThenElse tes = compileElims tes >>= \case
  -- fully applied
  b : t : f : es' -> return $ Hs.If () b t f `eApp` es'
  -- partially applied
  _ -> genericError "if_then_else_ must be fully applied"


-- | Compile @case_of_@ to Haskell @\case@ expression.
caseOf :: TElims -> C (Hs.Exp ())
caseOf tes = compileElims tes >>= \case
  -- applied to pattern lambda (that we remove, hence decrementLCase)
  e : Hs.LCase _ alts : es' -> decrementLCase $> eApp (Hs.Case () e alts) es'
  -- applied to regular lambda
  e : Hs.Lambda _ (p : ps) b : es' ->
    let lam [] = id
        lam qs = Hs.Lambda () qs
    in return $ eApp (Hs.Case () e [Hs.Alt () p (Hs.UnGuardedRhs () $ lam ps b) Nothing]) es'
  _ -> genericError "case_of_ must be fully applied to a lambda term."


-- TODO(flupe)
-- | Compile @the@ to an explicitly-annotated Haskell expression.
-- expTypeSig :: TElims -> C (Hs.Exp ())
-- expTypeSig tes = compileElims tes >>= \case
  
  -- case tes of
  --   _ : (_, typArg) : (_, expArg) : tes' -> do
  --     exp      <- compileTerm undefined (unArg expArg)
  --     typ      <- compileType (unArg typArg)
  --     compArgs <- compileArgs args'
  --     return $ eApp (Hs.ExpTypeSig () exp typ) compArgs
  --   _ -> genericError "`the` must be fully applied"


-- | Utility for translating class methods to special Haskell counterpart.
-- This runs an instance check.
specialClassFunction :: Hs.Exp () -> ([Hs.Exp ()] -> Hs.Exp ()) -> TElims -> C (Hs.Exp ())
specialClassFunction v f [] = return v
specialClassFunction v f ((t, w) : tes) = do
  checkInstance w
  f <$> compileElims tes -- TODO: tel

specialClassFunction1 :: Hs.Exp () -> (Hs.Exp () -> Hs.Exp ()) -> TElims -> C (Hs.Exp ())
specialClassFunction1 v f = specialClassFunction v $ \case
  (a : es) -> f a `eApp` es
  []       -> v

specialClassFunction2 :: Hs.Exp () -> (Hs.Exp () -> Hs.Exp () -> Hs.Exp ()) -> TElims -> C (Hs.Exp ())
specialClassFunction2 v f = specialClassFunction v $ \case
  (a : b : es) -> f a b `eApp` es
  es           -> v `eApp` es

specialClassFunction3 :: Hs.Exp () -> (Hs.Exp () -> Hs.Exp () -> Hs.Exp () -> Hs.Exp ()) -> TElims -> C (Hs.Exp ())
specialClassFunction3 v f = specialClassFunction v $ \case
  (a : b : c : es) -> f a b c `eApp` es
  es               -> v `eApp` es


mkEnumFrom :: TElims -> C (Hs.Exp ())
mkEnumFrom = specialClassFunction1 (hsVar "enumFrom") $ Hs.EnumFrom ()

mkEnumFromTo :: TElims -> C (Hs.Exp ())
mkEnumFromTo = specialClassFunction2 (hsVar "enumFromTo") $ Hs.EnumFromTo ()

mkEnumFromThen :: TElims -> C (Hs.Exp ())
mkEnumFromThen = specialClassFunction2 (hsVar "enumFromThen") $ Hs.EnumFromThen ()

mkEnumFromThenTo :: TElims -> C (Hs.Exp ())
mkEnumFromThenTo = specialClassFunction3 (hsVar "enumFromThenTo") $ Hs.EnumFromThenTo ()


fromNat :: TElims -> C (Hs.Exp ())
fromNat = specialClassFunction1 (hsVar "fromIntegral") $ \case
  n@Hs.Lit{} -> n
  v          -> hsVar "fromIntegral" `eApp` [v]

fromNeg :: TElims -> C (Hs.Exp ())
fromNeg = specialClassFunction1 negFromIntegral $ \case
  n@Hs.Lit{} -> Hs.NegApp () n
  v          -> negFromIntegral `eApp` [v]
  where
    negFromIntegral = hsVar "negate" `o` hsVar "fromIntegral"
    f `o` g = Hs.InfixApp () f (Hs.QVarOp () $ hsUnqualName "_._") g

fromString :: TElims -> C (Hs.Exp ())
fromString = specialClassFunction1 (hsVar "fromString") $ \case
  s@Hs.Lit{} -> s
  v          -> hsVar "fromString" `eApp` [v]


-- | Compile monadic bind operator _>>=_ to Haskell do notation.
monadBind :: TElims -> C (Hs.Exp ())
monadBind [] = return $ hsVar "_>>=_"
monadBind ((_, e):tes) = do
  checkInstance e
  compileElims tes >>= \case
    [u, Hs.Lambda _ [p] v] -> return (bind' u p v)
    [u, Hs.LCase () [Hs.Alt () p (Hs.UnGuardedRhs () v) Nothing]] ->
      decrementLCase >> return (bind' u p v)
    vs -> return $ hsVar "_>>=_" `eApp` vs
  where
    bind' :: Hs.Exp () -> Hs.Pat () -> Hs.Exp () -> Hs.Exp ()
    bind' u p v =
      let stmt1 = Hs.Generator () p u in
      case v of
        Hs.Do _ stmts -> Hs.Do () (stmt1 : stmts)
        _             -> Hs.Do () [stmt1, Hs.Qualifier () v]

-- | Compile monadic bind operator _>>_ to Haskell do notation.
monadSeq :: TElims -> C (Hs.Exp ())
monadSeq [] = return $ hsVar "_>>_"
monadSeq ((_, e):tes) = do
  checkInstance e
  compileElims tes >>= \case
    (u : v : vs) -> do
      let stmt1 = Hs.Qualifier () u
      case v of
        Hs.Do _ stmts -> return $ Hs.Do () (stmt1 : stmts)
        _             -> return $ Hs.Do () [stmt1, Hs.Qualifier () v]
    vs -> return $ hsVar "_>>_" `eApp` vs
-}

-- * Compilation of special constructors

-- | Custom compilation rules for special constructors.
isSpecialCon :: QName -> Maybe (TElims -> C (Hs.Exp ()))
isSpecialCon = prettyShow >>> \case
  "Haskell.Prim.Tuple._,_"  -> Just tupleTerm
  _                         -> Nothing

tupleTerm :: TElims -> C (Hs.Exp ())
tupleTerm tes = Hs.Tuple () Hs.Boxed . onlyArgs <$> compileElims tes
{-
isSpecialCon = prettyShow >>> \case
  "Haskell.Prim.Tuple._,_"          -> Just tupleTerm
  "Haskell.Prim.Tuple._×_×_._,_,_"  -> Just tupleTerm
  "Haskell.Extra.Erase.Erased"      -> Just erasedTerm
  "Haskell.Extra.Delay.Delay.now"   -> Just compileErasedApp
  "Haskell.Extra.Delay.Delay.later" -> Just compileErasedApp
  _                                 -> Nothing


erasedTerm :: TElims -> C (Hs.Exp ())
erasedTerm _ = tupleTerm []

-- | @compileErasedApp@ compiles the application of unboxed constructors,
-- unboxed projections and transparent functions.
-- Precondition is that at most one elim is preserved.
compileErasedApp :: TElims -> C (Hs.Exp ())
compileErasedApp tes = do
  reportSDoc "agda2hs.compile.term" 12 $
    text "Compiling application of transparent function or erased unboxed constructor"
  compileElims tes >>= \case
    []  -> return $ hsVar "id"
    [v] -> return v
    _   -> __IMPOSSIBLE__

-}
-- TODO(flupe):
-- maybeUnfoldCopy f es compileTerm $ \f es ->

-- | Compile a definition.
compileDef :: QName -> TElims ->  C (Hs.Exp ())
compileDef f tes | Just sem <- isSpecialDef f = do
  reportSDoc "agda2hs.compile.term" 12 $ text "Compiling application of special function"
  sem tes

compileDef f tes = do
  -- ifM (isClassFunction f) (compileClassFunApp f es) $
  -- ifM ((isJust <$> isUnboxProjection f) `or2M` isTransparentFunction f) (compileErasedApp tel es) $ do
  --   -- ifM (isInlinedFunction f) (compileInlineFunctionApp f es) $ do
    reportSDoc "agda2hs.compile.term" 12 $ text "Compiling application of regular function"

    -- Drop module parameters of local `where` functions
    -- TODO(flupe)
    -- moduleArgs <- getDefFreeVars f
    -- reportSDoc "agda2hs.compile.term" 15 $ text "Module arguments for" <+> (prettyTCM f <> text ":") <+> prettyTCM moduleArgs

    hsName <- compileQName f

    compileApp (Hs.Var () hsName) tes -- (drop moduleArgs tes)



compileCon :: ConHead -> ConInfo -> TElims -> C (Hs.Exp ())
compileCon h i tes
  | Just semantics <- isSpecialCon (conName h)
  = semantics tes
compileCon h i tes = do
  con <- Hs.Con () <$> compileQName (conName h)
  compileApp con tes
  -- isUnboxConstructor (conName h) >>= \case
  --   Just _  -> compileErasedApp tes
  --   Nothing -> (`compileApp` tes) . Hs.Con () =<< compileQName (conName h)

-- * Term compilation

compileTerm :: Type -> Term -> C (Hs.Exp ())
compileTerm ty v = do

  reportSDoc "agda2hs.compile" 7 $ text "compiling term:" <+> prettyTCM v
  reportSDoc "agda2hs.compile" 27 $ text "compiling term:" <+> pure (P.pretty $ unSpine1 v)

  -- NOTE: we DON'T UNSPINE here, in order to be able to propagate the type of projections properly.
  case v of

    Var i es -> do
      reportSDoc "agda2hs.compile.term" 50 $ text "Reached variable"
      varName <- compileDBVar i
      varType <- typeOfBV i
      compileApp (hsVar varName) (varType, Var i, es)

    Def f es -> do
      reportSDoc "agda2hs.compile.term" 50 $ text "Reached definition: " <+> prettyTCM f
      fType <- defType <$> getConstInfo f
      compileDef f (fType, Def f, es)

    Con ch ci es -> do
      reportSDoc "agda2hs.compile.term" 50 $ text "Reached constructor:" <+> prettyTCM (conName ch)
      Just ((_, _, args), ty) <- getConType ch ty
      compileCon ch ci (ty, Con ch ci, es)
      -- TODO(flupe:)
      -- -- the constructor may be a copy introduced by module application,
      -- -- therefore we need to find the original constructor
      -- info <- getConstInfo (conName h)
      -- if not (defCopy info)
      --   then compileCon h i es
      --   else let Constructor{conSrcCon = c} = theDef info in
      --        compileCon c ConOSystem es

    Lit l -> compileLiteral l

    Lam v b -> do
      reportSDoc "agda2hs.compile.term" 50 $ text "Reached lambda"
      compileLam ty v b

    t -> genericDocError =<< text "bad term:" <?> prettyTCM t


-- | Check whether a domain is usable on the Haskell side.
--
-- That is the case if:
-- * it is usable on the Agda side (i.e neither erased nor irrelevant).
-- * is not of sort Prop.
usableDom :: Dom Type -> Bool
usableDom dom | Prop _ <- getSort dom = False
usableDom dom = usableModality dom


compileLam :: Type -> ArgInfo -> Abs Term -> C (Hs.Exp ())
compileLam ty argi abs =
  reduce (unEl ty) >>= \case
    Pi dom cod -> do
      -- unusable domain, we remove the lambda and compile the body only
      if not (usableDom dom) then
        addContext dom $ compileTerm (absBody cod) (absBody abs)

      -- usable domain, user-written lambda is preserved
      else if getOrigin argi == UserWritten then do
        when (patternInTeleName `isPrefixOf` absName abs) $ genericDocError =<<
          text "Record pattern translation not supported. Use a pattern matching lambda instead."

        reportSDoc "agda2hs.compile" 17 $ text "compiling regular lambda"

        let varName = absName abs
            ctxElt  = (varName,) <$> dom

        hsLambda varName <$> addContext ctxElt (compileTerm (absBody cod) (absBody abs))

      -- usable domain, generated lambda means we introduce a section
      else undefined
        -- TODO
        --   -- System-inserted lambda, no need to preserve the name.
        --   underAbstraction_ b $ \ body -> do
        --     x <- showTCM (Var 0 [])
        --     let hsx = hsVar x
        --     body <- compileTerm body
        --     return $ case body of
        --       Hs.InfixApp _ a op b | a == hsx ->
        --         if pp op == "-" then -- Jesper: no right section for minus, as Haskell parses this as negation!
        --           Hs.LeftSection () b (Hs.QConOp () $ Hs.UnQual () $ hsName "subtract")
        --         else
        --           Hs.RightSection () op b -- System-inserted visible lambdas can only come from sections
        --       _            -> hsLambda x body         -- so we know x is not free in b.
       -- ^ TODO(flupe): ensure that it is bound properly if Abs Term and Abs Type don't bind the same

    _ -> do
      reportSDoc "agda2hs.compile" 17 $ text "Lambda type:" <+> prettyTCM ty
      __IMPOSSIBLE__



{-
-- | Compile the application of a function definition marked as inlinable.
-- The provided arguments will get substituted in the function body, and the missing arguments
-- will get quantified with lambdas.
compileInlineFunctionApp :: QName -> Elims -> C (Hs.Exp ())
compileInlineFunctionApp f es = do
  reportSDoc "agda2hs.compile.term" 12 $ text "Compiling application of inline function"
  Function { funClauses = cs } <- theDef <$> getConstInfo f
  let [ Clause { namedClausePats = pats } ] = filter (isJust . clauseBody) cs
  etaExpand (drop (length es) pats) es >>= compileTerm
  where
    -- inline functions can only have transparent constructor patterns and variable patterns
    extractPatName :: DeBruijnPattern -> ArgName
    extractPatName (VarP _ v) = dbPatVarName v
    extractPatName (ConP _ _ args) =
      let arg = namedThing $ unArg $ head $ filter (usableModality `and2M` visible) args
      in extractPatName arg
    extractPatName _ = __IMPOSSIBLE__

    extractName :: NamedArg DeBruijnPattern -> ArgName
    extractName (unArg -> np)
      | Just n <- nameOf np = rangedThing (woThing n)
      | otherwise = extractPatName (namedThing np)

    etaExpand :: NAPs -> Elims -> C Term
    etaExpand [] es = do
      r <- liftReduce 
            $ locallyReduceDefs (OnlyReduceDefs $ Set.singleton f)
            $ unfoldDefinitionStep (Def f es) f es
      case r of
        YesReduction _ t -> pure t
        _ -> genericDocError =<< text "Could not reduce inline function" <+> prettyTCM f

    etaExpand (p:ps) es =
      let ai = argInfo p in
      Lam ai . mkAbs (extractName p)
        <$> etaExpand ps (raise 1 es ++ [ Apply $ Arg ai $ var 0 ])
-}

-- `compileClassFunApp` is used when we have a record projection and we want to
-- drop the first visible arg (the record)
-- compileClassFunApp :: QName -> Elims -> C (Hs.Exp ())
-- compileClassFunApp f es = do
--   reportSDoc "agda2hs.compile.term" 14 $ text "Compiling application of class function"
--   hf <- compileQName f
--   case dropWhile notVisible (fromMaybe __IMPOSSIBLE__ $ allApplyElims es) of
--     []     -> __IMPOSSIBLE__
--     (x:xs) -> do
--       curMod <- currentModule
--       reportSDoc "agda2hs.compile" 15 $ nest 2 $ vcat
--         [ text "symbol module:  " <+> prettyTCM (qnameModule f)
--         , text "current module: " <+> prettyTCM curMod
--         ]
--       unless (curMod `isLeChildModuleOf` qnameModule f) $ checkInstance $ unArg x
--       args <- compileArgs xs
--       return $ Hs.Var () hf `eApp` args

compileApp :: Hs.Exp () -> TElims -> C (Hs.Exp ())
compileApp hd tes = appCompiledElims hd <$> compileElims tes
  -- NOTE(flupe): probably not that efficient
  where appCompiledElims :: Hs.Exp () -> [CompiledElim] -> Hs.Exp ()
        appCompiledElims x []              = x
        appCompiledElims x (EArg  y : ces) = appCompiledElims (eApp x [y]) ces
        appCompiledElims x (EProj p : ces) = appCompiledElims (eApp p [x]) ces

-- | Elims get compiled to arguments or projections.
-- We ignore path applications.
data CompiledElim = EArg (Hs.Exp ()) | EProj (Hs.Exp ())

compileElims :: TElims -> C [CompiledElim]
compileElims (ty, term, []) = pure []
compileElims (ty, term, Apply at : es) | Pi a b <- unEl ty = do
  let rest = compileElims (absApp b (unArg at), term . (Apply at:), es)
  compiledDom a >>= \case
    DODropped  -> rest
    DOInstance -> checkInstance (unArg at) *> rest
    DOKept     -> (:) <$> (EArg <$> compileTerm (unDom a) (unArg at))
                      <*> rest
compileElims (ty, term, Proj po pn : es) = do
  ty' <- shouldBeProjectible (term []) ty po pn
  (:) <$> (EProj . Hs.Var () <$> compileQName pn) <*> compileElims (ty', term . (Proj po pn:), es)
  -- TODO(flupe): should we check whether the projection is erased?
compileElims _ = __IMPOSSIBLE__ -- cubical endpoint application not supported

onlyArgs :: [CompiledElim] -> [Hs.Exp()]
onlyArgs [] = []
onlyArgs (EArg x:ces) = x:onlyArgs ces
onlyArgs _ = __IMPOSSIBLE__

{-
clauseToAlt :: Hs.Match () -> C (Hs.Alt ())
clauseToAlt (Hs.Match _ _ [p] rhs wh) = pure $ Hs.Alt () p rhs wh
clauseToAlt (Hs.Match _ _ ps _ _)     = genericError "Pattern matching lambdas must take a single argument"
clauseToAlt Hs.InfixMatch{}           = __IMPOSSIBLE__
-}

compileLiteral :: Literal -> C (Hs.Exp ())
compileLiteral (LitNat n)    = return $ Hs.intE n
compileLiteral (LitFloat d)  = return $ Hs.Lit () $ Hs.Frac () (toRational d) (show d)
compileLiteral (LitWord64 w) = return $ Hs.Lit () $ Hs.PrimWord () (fromIntegral w) (show w)
compileLiteral (LitChar c)   = return $ Hs.charE c
compileLiteral (LitString t) = return $ Hs.Lit () $ Hs.String () s s
  where s = Text.unpack t
compileLiteral l             = genericDocError =<< text "bad term:" <?> prettyTCM (Lit l)
