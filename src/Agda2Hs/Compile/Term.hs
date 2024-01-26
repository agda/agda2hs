{-# LANGUAGE ViewPatterns, NamedFieldPuns #-}
module Agda2Hs.Compile.Term
  ( compileTerm
  ) where

import Control.Arrow ( (>>>), (&&&) )
import Control.Monad ( unless )
import Control.Monad.Reader

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
import Agda.TypeChecking.Reduce ( unfoldDefinitionStep )
import Agda.TypeChecking.Substitute ( Apply(applyE), raise, mkAbs )

import Agda.Utils.Lens

import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.Monad
import Agda.Utils.Size

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name ( compileQName )

import Agda2Hs.Compile.Type ( compileType )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.Compile.Var ( compileDBVar )
import Agda2Hs.HsUtils

import {-# SOURCE #-} Agda2Hs.Compile.Function ( compileClause' )


-- * Compilation of special definitions

-- | Custom compilation rules for special definitions.
isSpecialTerm :: QName -> Maybe (Elims -> C (Hs.Exp ()))
isSpecialTerm q = case prettyShow q of
  _ | isExtendedLambdaName q                    -> Just (lambdaCase q)
  "Haskell.Prim.if_then_else_"                  -> Just ifThenElse
  "Haskell.Prim.case_of_"                       -> Just caseOf
  "Haskell.Prim.the"                            -> Just expTypeSig
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


-- | Compile a lambda-case to the equivalent @\case@ expression.
lambdaCase :: QName -> Elims -> C (Hs.Exp ())
lambdaCase q es = setCurrentRangeQ q $ do
  Function{funClauses = cls, funExtLam = Just ExtLamInfo {extLamModule = mname}}
    <- theDef <$> getConstInfo q
  npars <- size <$> lookupSection mname
  let (pars, rest) = splitAt npars es
      cs           = applyE cls pars
  cs <- mapMaybeM (compileClause' (qnameModule q) $ hsName "(lambdaCase)") cs
  case cs of
    -- If there is a single clause and all patterns got erased, we
    -- simply return the body.
    [Hs.Match _ _ [] (Hs.UnGuardedRhs _ rhs) _] -> return rhs
    _ -> do
      lcase <- hsLCase =<< mapM clauseToAlt cs -- Pattern lambdas cannot have where blocks
      eApp lcase <$> compileElims rest


-- | Compile @if_then_else_@ to a Haskell @if ... then ... else ... @ expression.
ifThenElse :: Elims -> C (Hs.Exp ())
ifThenElse es = compileElims es >>= \case
  -- fully applied
  b : t : f : es' -> return $ Hs.If () b t f `eApp` es'
  -- partially applied
  _ -> genericError $ "if_then_else_ must be fully applied"


-- | Compile @case_of_@ to Haskell @\case@ expression.
caseOf :: Elims -> C (Hs.Exp ())
caseOf es = compileElims es >>= \case
  -- applied to pattern lambda (that we remove, hence decrementLCase)
  e : Hs.LCase _ alts : es' -> decrementLCase $> eApp (Hs.Case () e alts) es'
  -- applied to regular lambda
  e : Hs.Lambda _ (p : ps) b : es' ->
    let lam [] = id
        lam qs = Hs.Lambda () qs
    in return $ eApp (Hs.Case () e [Hs.Alt () p (Hs.UnGuardedRhs () $ lam ps b) Nothing]) es'
  _ -> genericError "case_of_ must be fully applied to a lambda term."


-- | Compile @the@ to an explicitly-annotated Haskell expression.
expTypeSig :: Elims -> C (Hs.Exp ())
expTypeSig es = do
  let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
  case args of
    _ : typArg : expArg : args' -> do         -- the first one is the level; we throw that away
      exp <- compileTerm $ unArg expArg -- this throws an error if it was Nothing
      typ <- compileType (unArg typArg)
      compArgs <- compileArgs args'
      return $ eApp (Hs.ExpTypeSig () exp typ) compArgs
    _ -> genericError $ "`the` must be fully applied"


-- | Utility for translating class methods to special Haskell counterpart.
-- This runs an instance check.
specialClassFunction :: Hs.Exp () -> ([Hs.Exp ()] -> Hs.Exp ()) -> Elims -> C (Hs.Exp ())
specialClassFunction v f [] = return v
specialClassFunction v f (Apply w : es) = do
  checkInstance $ unArg w
  f <$> compileElims es
specialClassFunction v f (_ : _) = __IMPOSSIBLE__

specialClassFunction1 :: Hs.Exp () -> (Hs.Exp () -> Hs.Exp ()) -> Elims -> C (Hs.Exp ())
specialClassFunction1 v f = specialClassFunction v $ \case
  (a : es) -> f a `eApp` es
  []       -> v

specialClassFunction2 :: Hs.Exp () -> (Hs.Exp () -> Hs.Exp () -> Hs.Exp ()) -> Elims -> C (Hs.Exp ())
specialClassFunction2 v f = specialClassFunction v $ \case
  (a : b : es) -> f a b `eApp` es
  es           -> v `eApp` es

specialClassFunction3 :: Hs.Exp () -> (Hs.Exp () -> Hs.Exp () -> Hs.Exp () -> Hs.Exp ()) -> Elims -> C (Hs.Exp ())
specialClassFunction3 v f = specialClassFunction v $ \case
  (a : b : c : es) -> f a b c `eApp` es
  es               -> v `eApp` es


mkEnumFrom :: Elims -> C (Hs.Exp ())
mkEnumFrom = specialClassFunction1 (hsVar "enumFrom") $ Hs.EnumFrom ()

mkEnumFromTo :: Elims -> C (Hs.Exp ())
mkEnumFromTo = specialClassFunction2 (hsVar "enumFromTo") $ Hs.EnumFromTo ()

mkEnumFromThen :: Elims -> C (Hs.Exp ())
mkEnumFromThen = specialClassFunction2 (hsVar "enumFromThen") $ Hs.EnumFromThen ()

mkEnumFromThenTo :: Elims -> C (Hs.Exp ())
mkEnumFromThenTo = specialClassFunction3 (hsVar "enumFromThenTo") $ Hs.EnumFromThenTo ()


fromNat :: Elims -> C (Hs.Exp ())
fromNat = specialClassFunction1 (hsVar "fromIntegral") $ \case
  n@Hs.Lit{} -> n
  v          -> hsVar "fromIntegral" `eApp` [v]

fromNeg :: Elims -> C (Hs.Exp ())
fromNeg = specialClassFunction1 negFromIntegral $ \case
  n@Hs.Lit{} -> Hs.NegApp () n
  v          -> negFromIntegral `eApp` [v]
  where
    negFromIntegral = hsVar "negate" `o` hsVar "fromIntegral"
    f `o` g = Hs.InfixApp () f (Hs.QVarOp () $ hsUnqualName "_._") g

fromString :: Elims -> C (Hs.Exp ())
fromString = specialClassFunction1 (hsVar "fromString") $ \case
  s@Hs.Lit{} -> s
  v          -> hsVar "fromString" `eApp` [v]


-- | Compile monadic bind operator _>>=_ to Haskell do notation.
monadBind :: Elims -> C (Hs.Exp ())
monadBind (e:es) = do
  checkInstance $ unArg $ isApplyElim' __IMPOSSIBLE__ e
  compileElims es >>= \case
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
monadBind [] = return $ hsVar "_>>=_"


-- | Compile monadic bind operator _>>_ to Haskell do notation.
monadSeq :: Elims -> C (Hs.Exp ())
monadSeq (e:es) = do
  checkInstance $ unArg $ isApplyElim' __IMPOSSIBLE__ e
  compileElims es >>= \case
    (u : v : vs) -> do
      let stmt1 = Hs.Qualifier () u
      case v of
        Hs.Do _ stmts -> return $ Hs.Do () (stmt1 : stmts)
        _             -> return $ Hs.Do () [stmt1, Hs.Qualifier () v]
    vs -> return $ hsVar "_>>_" `eApp` vs
monadSeq [] = return $ hsVar "_>>_"



-- * Compilation of special constructors

-- | Custom compilation rules for special constructors.
isSpecialCon :: QName -> Maybe (Elims -> C (Hs.Exp ()))
isSpecialCon = prettyShow >>> \case
  "Haskell.Prim.Tuple._,_"          -> Just tupleTerm
  "Haskell.Prim.Tuple._×_×_._,_,_"  -> Just tupleTerm
  "Haskell.Extra.Erase.Erased"      -> Just erasedTerm
  "Haskell.Extra.Delay.Delay.now"   -> Just compileErasedApp
  "Haskell.Extra.Delay.Delay.later" -> Just compileErasedApp
  _                                 -> Nothing

tupleTerm :: Elims -> C (Hs.Exp ())
tupleTerm es = compileElims es <&> Hs.Tuple () Hs.Boxed

erasedTerm :: Elims -> C (Hs.Exp ())
erasedTerm es = tupleTerm []

-- | @compileErasedApp@ compiles the application of unboxed constructors,
-- unboxed projections and transparent functions.
-- Precondition is that at most one elim is preserved.
compileErasedApp :: Elims -> C (Hs.Exp ())
compileErasedApp es = do
  reportSDoc "agda2hs.compile.term" 12 $
    text "Compiling application of transparent function or erased unboxed constructor"
  compileElims es >>= \case
    []  -> return $ hsVar "id"
    [v] -> return v
    _   -> __IMPOSSIBLE__

-- * Term compilation

compileTerm :: Term -> C (Hs.Exp ())
compileTerm v = do
  reportSDoc "agda2hs.compile" 7 $ text "compiling term:" <+> prettyTCM v
  reportSDoc "agda2hs.compile" 27 $ text "compiling term:" <+> pure (P.pretty $ unSpine1 v)
  case unSpine1 v of
    Var x es   -> do
      s <- compileDBVar x
      hsVar s `app` es
    -- v currently we assume all record projections are instance
    -- args that need attention
    Def f es -> maybeUnfoldCopy f es compileTerm $ \f es -> if
      | Just semantics <- isSpecialTerm f -> do
          reportSDoc "agda2hs.compile.term" 12 $ text "Compiling application of special function"
          semantics es
      | otherwise ->
          ifM (isClassFunction f) (compileClassFunApp f es) $
          ifM ((isJust <$> isUnboxProjection f) `or2M` isTransparentFunction f) (compileErasedApp es) $
          ifM (isInlinedFunction f) (compileInlineFunctionApp f es) $ do
            reportSDoc "agda2hs.compile.term" 12 $ text "Compiling application of regular function"
            -- Drop module parameters of local `where` functions
            moduleArgs <- getDefFreeVars f
            reportSDoc "agda2hs.compile.term" 15 $ text "Module arguments for" <+> (prettyTCM f <> text ":") <+> prettyTCM moduleArgs
            (`app` drop moduleArgs es) . Hs.Var () =<< compileQName f
    Con h i es -> do
      reportSDoc "agda2hs.compile" 8 $ text "reached constructor:" <+> prettyTCM (conName h)
      -- the constructor may be a copy introduced by module application,
      -- therefore we need to find the original constructor
      info <- getConstInfo (conName h)
      if not (defCopy info)
        then compileCon h i es
        else let Constructor{conSrcCon = c} = theDef info in
             compileCon c ConOSystem es
    Lit l -> compileLiteral l
    Lam v b | usableModality v, getOrigin v == UserWritten -> do
      when (patternInTeleName `isPrefixOf` absName b) $ genericDocError =<< do
        text "Record pattern translation not supported. Use a pattern matching lambda instead."
      unless (visible v) $ genericDocError =<< do
        text "Implicit lambda not supported: " <+> prettyTCM (absName b)
      hsLambda (absName b) <$> underAbstr_ b compileTerm
    Lam v b | usableModality v ->
      -- System-inserted lambda, no need to preserve the name.
      underAbstraction_ b $ \ body -> do
        x <- showTCM (Var 0 [])
        body <- compileTerm body
        return $ case body of
          Hs.InfixApp _ a op b | a == hsVar x ->
            if pp op == "-" then -- Jesper: no right section for minus, as Haskell parses this as negation!
              Hs.LeftSection () b (Hs.QConOp () $ Hs.UnQual () $ hsName "subtract")
            else                       -- System-inserted visible lambdas can only come from sections
              Hs.RightSection () op b  -- so we know x is not free in b.
          _            -> hsLambda x body         
    Lam v b ->
      -- Drop erased lambdas (#65)
      underAbstraction_ b $ \ body -> compileTerm body
    t -> genericDocError =<< text "bad term:" <?> prettyTCM t
  where
    app :: Hs.Exp () -> Elims -> C (Hs.Exp ())
    app hd es = eApp hd <$> compileElims es

    compileCon :: ConHead -> ConInfo -> Elims -> C (Hs.Exp ())
    compileCon h i es
      | Just semantics <- isSpecialCon (conName h)
      = semantics es
    compileCon h i es =
      isUnboxConstructor (conName h) >>= \case
        Just _  -> compileErasedApp es
        Nothing -> (`app` es) . Hs.Con () =<< compileQName (conName h)


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

-- `compileClassFunApp` is used when we have a record projection and we want to
-- drop the first visible arg (the record)
compileClassFunApp :: QName -> Elims -> C (Hs.Exp ())
compileClassFunApp f es = do
  reportSDoc "agda2hs.compile.term" 14 $ text "Compiling application of class function"
  hf <- compileQName f
  case dropWhile notVisible (fromMaybe __IMPOSSIBLE__ $ allApplyElims es) of
    []     -> __IMPOSSIBLE__
    (x:xs) -> do
      curMod <- currentModule
      reportSDoc "agda2hs.compile" 15 $ nest 2 $ vcat
        [ text "symbol module:  " <+> prettyTCM (qnameModule f)
        , text "current module: " <+> prettyTCM curMod
        ]
      unless (curMod `isLeChildModuleOf` qnameModule f) $ checkInstance $ unArg x
      args <- compileArgs xs
      return $ Hs.Var () hf `eApp` args

compileElims :: Elims -> C [Hs.Exp ()]
compileElims es = compileArgs $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es

compileArgs :: Args -> C [Hs.Exp ()]
compileArgs args = mapMaybeM compileArg args

compileArg :: Arg Term -> C (Maybe (Hs.Exp ()))
compileArg x = do
  reportSDoc "agda2hs.compile" 8 $ text "compiling argument" <+> prettyTCM x
  if | keepArg x -> Just <$> compileTerm (unArg x)
     | isInstance x, usableModality x -> Nothing <$ checkInstance (unArg $ x)
     | otherwise -> return Nothing

clauseToAlt :: Hs.Match () -> C (Hs.Alt ())
clauseToAlt (Hs.Match _ _ [p] rhs wh) = pure $ Hs.Alt () p rhs wh
clauseToAlt (Hs.Match _ _ ps _ _)     = genericError "Pattern matching lambdas must take a single argument"
clauseToAlt Hs.InfixMatch{}           = __IMPOSSIBLE__

compileLiteral :: Literal -> C (Hs.Exp ())
compileLiteral (LitNat n)    = return $ Hs.intE n
compileLiteral (LitFloat d)  = return $ Hs.Lit () $ Hs.Frac () (toRational d) (show d)
compileLiteral (LitWord64 w) = return $ Hs.Lit () $ Hs.PrimWord () (fromIntegral w) (show w)
compileLiteral (LitChar c)   = return $ Hs.charE c
compileLiteral (LitString t) = return $ Hs.Lit () $ Hs.String () s s
  where s = Text.unpack t
compileLiteral l               = genericDocError =<< text "bad term:" <?> prettyTCM (Lit l)
