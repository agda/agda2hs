module Agda2Hs.Compile.Term where

import Control.Arrow ( (>>>), (&&&) )
import Control.Monad ( unless )
import Control.Monad.Reader

import Data.List ( isPrefixOf )
import Data.Maybe ( fromMaybe, isJust )
import qualified Data.Text as Text ( unpack )

import qualified Language.Haskell.Exts as Hs

import Agda.Syntax.Common.Pretty ( prettyShow )
import qualified Agda.Syntax.Common.Pretty as P
import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce ( instantiate )
import Agda.TypeChecking.Substitute ( Apply(applyE) )

import Agda.Utils.Lens

import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.Monad
import Agda.Utils.Size

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name ( compileQName )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

import {-# SOURCE #-} Agda2Hs.Compile.Function ( compileClause' )

isSpecialTerm :: QName -> Maybe (QName -> Elims -> C (Hs.Exp ()))
isSpecialTerm q = case prettyShow q of
  _ | isExtendedLambdaName q                    -> Just lambdaCase
  "Haskell.Prim.if_then_else_"                  -> Just ifThenElse
  "Haskell.Prim.Enum.Enum.enumFrom"             -> Just mkEnumFrom
  "Haskell.Prim.Enum.Enum.enumFromTo"           -> Just mkEnumFromTo
  "Haskell.Prim.Enum.Enum.enumFromThen"         -> Just mkEnumFromThen
  "Haskell.Prim.Enum.Enum.enumFromThenTo"       -> Just mkEnumFromThenTo
  "Haskell.Prim.case_of_"                       -> Just caseOf
  "Haskell.Prim.Monad.Do.Monad._>>=_"           -> Just bind
  "Haskell.Prim.Monad.Do.Monad._>>_"            -> Just sequ
  "Agda.Builtin.FromNat.Number.fromNat"         -> Just fromNat
  "Agda.Builtin.FromNeg.Negative.fromNeg"       -> Just fromNeg
  "Agda.Builtin.FromString.IsString.fromString" -> Just fromString
  _                                             -> Nothing

isSpecialCon :: QName -> Maybe (ConHead -> ConInfo -> Elims -> C (Hs.Exp ()))
isSpecialCon = prettyShow >>> \case
  "Haskell.Prim.Tuple._;_" -> Just tupleTerm
  _ -> Nothing

tupleTerm :: ConHead -> ConInfo -> Elims -> C (Hs.Exp ())
tupleTerm cons i es = do
  let v   = Con cons i es
      err = sep [ text "Tuple value"
                , nest 2 $ prettyTCM v
                , text "does not have a known size." ]
  xs <- makeList' "Agda.Builtin.Unit.tt" "Haskell.Prim.Tuple._;_" err v
  ts <- mapM compileTerm xs
  return $ Hs.Tuple () Hs.Boxed ts

ifThenElse :: QName -> Elims -> C (Hs.Exp ())
ifThenElse _ es = compileElims es >>= \case
  -- fully applied
  b : t : f : es' -> return $ Hs.If () b t f `eApp` es'
  -- partially applied
  _ -> genericError $ "if_then_else must be fully applied"

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

fromNat :: QName -> Elims -> C (Hs.Exp ())
fromNat _ = specialClassFunction1 (hsVar "fromIntegral") $ \case
  n@Hs.Lit{} -> n
  v          -> hsVar "fromIntegral" `eApp` [v]

fromNeg :: QName -> Elims -> C (Hs.Exp ())
fromNeg _ = specialClassFunction1 negFromIntegral $ \case
  n@Hs.Lit{} -> Hs.NegApp () n
  v          -> negFromIntegral `eApp` [v]
  where
    negFromIntegral = hsVar "negate" `o` hsVar "fromIntegral"
    f `o` g = Hs.InfixApp () f (Hs.QVarOp () $ hsUnqualName "_._") g

fromString :: QName -> Elims -> C (Hs.Exp ())
fromString _ = specialClassFunction1 (hsVar "fromString") $ \case
  s@Hs.Lit{} -> s
  v          -> hsVar "fromString" `eApp` [v]

mkEnumFrom :: QName -> Elims -> C (Hs.Exp ())
mkEnumFrom _ = specialClassFunction1 (hsVar "enumFrom") $
  \a -> Hs.EnumFrom () a

mkEnumFromTo :: QName -> Elims -> C (Hs.Exp ())
mkEnumFromTo _ = specialClassFunction2 (hsVar "enumFromTo") $
  \a b -> Hs.EnumFromTo () a b

mkEnumFromThen :: QName -> Elims -> C (Hs.Exp ())
mkEnumFromThen _ = specialClassFunction2 (hsVar "enumFromThen") $
  \a b -> Hs.EnumFromThen () a b

mkEnumFromThenTo :: QName -> Elims -> C (Hs.Exp ())
mkEnumFromThenTo _ = specialClassFunction3 (hsVar "enumFromThenTo") $
  \a b c -> Hs.EnumFromThenTo () a b c

delay :: QName -> Elims -> C (Hs.Exp ())
delay _ = compileErasedApp

force :: QName -> Elims -> C (Hs.Exp ())
force _ = compileErasedApp

bind :: QName -> Elims -> C (Hs.Exp ())
bind q (e:es) = do
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
bind q [] = return $ hsVar "_>>=_"

sequ :: QName -> Elims -> C (Hs.Exp ())
sequ q (e:es) = do
  checkInstance $ unArg $ isApplyElim' __IMPOSSIBLE__ e
  compileElims es >>= \case
    (u : v : vs) -> do
      let stmt1 = Hs.Qualifier () u
      case v of
        Hs.Do _ stmts -> return $ Hs.Do () (stmt1 : stmts)
        _             -> return $ Hs.Do () [stmt1, Hs.Qualifier () v]
    vs -> return $ hsVar "_>>_" `eApp` vs
sequ q [] = return $ hsVar "_>>_"

caseOf :: QName -> Elims -> C (Hs.Exp ())
caseOf _ es = compileElims es >>= \case
  -- applied to pattern lambda
  e : Hs.LCase _ alts : es' -> do
    decrementLCase
    return $ eApp (Hs.Case () e alts) es'
  -- applied to regular lambda
  e : Hs.Lambda _ (p : ps) b : es' -> do
    let lam [] = id
        lam qs = Hs.Lambda () qs
    return $ eApp (Hs.Case () e [Hs.Alt () p (Hs.UnGuardedRhs () $ lam ps b) Nothing]) es'
  -- applied to non-lambda / partially applied
  _ -> genericError $ "case_of_ must be fully applied to a lambda"

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

clauseToAlt :: Hs.Match () -> C (Hs.Alt ())
clauseToAlt (Hs.Match _ _ [p] rhs wh) = pure $ Hs.Alt () p rhs wh
clauseToAlt (Hs.Match _ _ ps _ _)     = genericError $ "Pattern matching lambdas must take a single argument"
clauseToAlt Hs.InfixMatch{}           = __IMPOSSIBLE__

compileLiteral :: Literal -> C (Hs.Exp ())
compileLiteral (LitNat n)    = return $ Hs.intE n
compileLiteral (LitFloat d)  = return $ Hs.Lit () $ Hs.Frac () (toRational d) (show d)
compileLiteral (LitWord64 w) = return $ Hs.Lit () $ Hs.PrimWord () (fromIntegral w) (show w)
compileLiteral (LitChar c)   = return $ Hs.charE c
compileLiteral (LitString t) = return $ Hs.Lit () $ Hs.String () s s
  where s = Text.unpack t
compileLiteral l               = genericDocError =<< text "bad term:" <?> prettyTCM (Lit l)

-- | Compile a variable. If the check is enabled, ensures the variable is usable and visible.
compileVar :: Nat -> C String
compileVar x = do
  (d, n) <- (fmap snd &&& fst . unDom) <$> lookupBV x
  let cn = prettyShow $ nameConcrete n
  let b | notVisible d   = "hidden"
        | hasQuantity0 d = "erased"
        | otherwise      = ""
  whenM (asks checkVar) $ unless (null b) $ genericDocError =<<
    text ("Cannot use " <> b <> " variable " <> cn)
  return cn

compileTerm :: Term -> C (Hs.Exp ())
compileTerm v = do
  reportSDoc "agda2hs.compile" 7 $ text "compiling term:" <+> prettyTCM v
  reportSDoc "agda2hs.compile" 27 $ text "compiling term:" <+> pure (P.pretty $ unSpine1 v)
  case unSpine1 v of
    Var x es   -> do
      s <- compileVar x
      hsVar s `app` es
    -- v currently we assume all record projections are instance
    -- args that need attention
    Def f es -> maybeUnfoldCopy f es compileTerm $ \f es -> if
      | Just semantics <- isSpecialTerm f -> do
          reportSDoc "agda2hs.compile.term" 12 $ text "Compiling application of special function"
          semantics f es
      | otherwise -> isClassFunction f >>= \case
          True  -> compileClassFunApp f es
          False -> (isJust <$> isUnboxProjection f) `or2M` isTransparentFunction f >>= \case
            True  -> compileErasedApp es
            False -> do
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
        let hsx = hsVar x
        body <- compileTerm body
        return $ case body of
          Hs.InfixApp _ a op b
            | a == hsx -> Hs.RightSection () op b -- System-inserted visible lambdas can only come from sections
          _            -> hsLambda x body         -- so we know x is not free in b.
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
      = semantics h i es
    compileCon h i es =
      isUnboxConstructor (conName h) >>= \case
        Just _  -> compileErasedApp es
        Nothing -> (`app` es) . Hs.Con () =<< compileQName (conName h)

-- `compileErasedApp` compiles an application of an erased constructor
-- or projection.
compileErasedApp :: Elims -> C (Hs.Exp ())
compileErasedApp es = do
  reportSDoc "agda2hs.compile.term" 12 $ text "Compiling application of erased function"
  compileElims es >>= \case
    []     -> return $ hsVar "id"
    (v:vs) -> return $ v `eApp` vs

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
