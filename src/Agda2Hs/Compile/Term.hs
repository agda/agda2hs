module Agda2Hs.Compile.Term where

import Control.Arrow ( (>>>) )
import Control.Monad ( unless )
import Control.Monad.Reader

import Data.List ( isPrefixOf )
import Data.Maybe ( fromMaybe, isJust )
import qualified Data.Text as Text ( unpack )

import qualified Language.Haskell.Exts as Hs

import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce ( instantiate )
import Agda.TypeChecking.Substitute ( Apply(applyE) )

import Agda.Utils.Lens
import Agda.Utils.Pretty ( prettyShow )
import qualified Agda.Utils.Pretty as P

import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.Monad
import Agda.Utils.Size

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name ( compileQName )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

import {-# SOURCE #-} Agda2Hs.Compile.Function ( compileClause )

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

fromNat :: QName -> Elims -> C (Hs.Exp ())
fromNat _ es = compileElims es <&> \case
  _ : n@Hs.Lit{} : es' -> n `eApp` es'
  es'                  -> hsVar "fromIntegral" `eApp` drop 1 es'

fromNeg :: QName -> Elims -> C (Hs.Exp ())
fromNeg _ es = compileElims es <&> \case
  _ : n@Hs.Lit{} : es' -> Hs.NegApp () n `eApp` es'
  es'                  -> (hsVar "negate" `o` hsVar "fromIntegral") `eApp` drop 1 es'
  where
    f `o` g = Hs.InfixApp () f (Hs.QVarOp () $ hsUnqualName "_._") g

fromString :: QName -> Elims -> C (Hs.Exp ())
fromString _ es = compileElims es <&> \case
  _ : s@Hs.Lit{} : es' -> s `eApp` es'
  es'                  -> hsVar "fromString" `eApp` drop 1 es'

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
  -- partially applied -> eta-expand
  es' -> do
    xs <- fmap Hs.name . drop (length es') <$> mapM freshString ["b", "t", "f"]
    let [b, t, f] = es' ++ map Hs.var xs
    return $ Hs.lamE (Hs.pvar <$> xs) $ Hs.If () b t f

mkEnumFrom :: QName -> Elims -> C (Hs.Exp ())
mkEnumFrom q es = compileElims es >>= \case
  _ : a : es' -> return $ Hs.EnumFrom () a `eApp` es'
  es'         -> return $ hsVar "enumFrom" `eApp` drop 1 es'

mkEnumFromTo :: QName -> Elims -> C (Hs.Exp ())
mkEnumFromTo q es = compileElims es >>= \case
  _ : a : b : es' -> return $ Hs.EnumFromTo () a b `eApp` es'
  es'             -> return $ hsVar "enumFromTo" `eApp` drop 1 es'

mkEnumFromThen :: QName -> Elims -> C (Hs.Exp ())
mkEnumFromThen q es = compileElims es >>= \case
  _ : a : a' : es' -> return $ Hs.EnumFromThen () a a' `eApp` es'
  es'              -> return $ hsVar "enumFromThen" `eApp` drop 1 es'

mkEnumFromThenTo :: QName -> Elims -> C (Hs.Exp ())
mkEnumFromThenTo q es = compileElims es >>= \case
  _ : a : a' : b : es' -> return $ Hs.EnumFromThenTo () a a' b `eApp` es'
  es'                  -> return $ hsVar "enumFromThenTo" `eApp` drop 1 es'

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
  -- no lambda, but fully applied: inline
  e : f : es' -> return $ eApp f $ e : es'
  -- partial application
  [e]         -> do
    let Just dollar = getOp (hsVar "_$_")
    return $ Hs.RightSection () dollar e
  -- unapplied
  []          -> return $ eApp (hsVar "flip") [hsVar "_$_"]

lambdaCase :: QName -> Elims -> C (Hs.Exp ())
lambdaCase q es = setCurrentRange (nameBindingSite $ qnameName q) $ do
  Function{funClauses = cls, funExtLam = Just ExtLamInfo {extLamModule = mname}}
    <- theDef <$> getConstInfo q
  npars <- size <$> lookupSection mname
  let (pars, rest) = splitAt npars es
      cs           = applyE cls pars
  ls   <- filter (`extLamUsedIn` cs) <$> asks locals
  cs   <- withLocals ls $ mapM (compileClause (qnameModule q) $ hsName "(lambdaCase)") cs
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

compileVar :: Nat -> C String
compileVar x = prettyShow . nameConcrete <$> nameOfBV x

compileTerm :: Term -> C (Hs.Exp ())
compileTerm v = do
  reportSDoc "agda2hs.compile" 7 $ text "compiling term:" <+> prettyTCM v
  reportSDoc "agda2hs.compile" 27 $ text "compiling term:" <+> pure (P.pretty v)
  case unSpine1 v of
    Var x es   -> do
      s <- compileVar x
      hsVar s `app` es
    -- v currently we assume all record projections are instance
    -- args that need attention
    Def f es
      | Just semantics <- isSpecialTerm f -> semantics f es
      | otherwise -> isClassFunction f >>= \case
        True  -> compileClassFunApp f es
        False -> (isJust <$> isUnboxProjection f) `or2M` isTransparentFunction f >>= \case
          True  -> compileErasedApp es
          False -> do
            -- Drop module parameters (unless projection-like)
            n <- (theDef <$> getConstInfo f) >>= \case
              Function{ funProjection = Right{} } -> return 0
              _ -> size <$> lookupSection (qnameModule f)
            (`app` drop n es) . Hs.Var () =<< compileQName f
    Con h i es
      | Just semantics <- isSpecialCon (conName h) -> semantics h i es
    Con h i es -> isUnboxConstructor (conName h) >>= \case
      Just _  -> compileErasedApp es
      Nothing -> (`app` es) . Hs.Con () =<< compileQName (conName h)
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
    app hd es = eApp <$> pure hd <*> compileElims es

-- `compileErasedApp` compiles an application of an erased constructor
-- or projection.
compileErasedApp :: Elims -> C (Hs.Exp ())
compileErasedApp es = compileElims es >>= \case
  []     -> return $ hsVar "id"
  (v:vs) -> return $ v `eApp` vs

-- `compileClassFunApp` is used when we have a record projection and we want to
-- drop the first visible arg (the record)
compileClassFunApp :: QName -> Elims -> C (Hs.Exp ())
compileClassFunApp f es = do
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
