{-# LANGUAGE TypeApplications #-}

module Agda2Hs.Compile.Type where

import Control.Arrow ( (>>>) )
import Control.Monad ( forM )
import Control.Monad.Reader ( asks )
import Data.Maybe ( mapMaybe )

import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Extension as Hs
import qualified Language.Haskell.Exts.Pretty as Hs

import Agda.Compiler.Backend hiding ( Args )

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce ( reduce )
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.Pretty ( prettyShow )
import Agda.Utils.List ( downFrom )
import Agda.Utils.Maybe ( ifJustM, fromMaybe )
import Agda.Utils.Monad ( forMaybeM, ifM, unlessM )
import Agda.Utils.Size ( Sized(size) )
import Agda.Utils.Functor ( ($>) )

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name ( compileQName )
import Agda2Hs.Compile.Term ( compileVar )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.AgdaUtils
import Agda2Hs.HsUtils

isSpecialType :: QName -> Maybe (QName -> Elims -> C (Hs.Type ()))
isSpecialType = prettyShow >>> \case
  "Haskell.Prim.Tuple.Tuple" -> Just tupleType
  "Haskell.Prim.Tuple._×_"   -> Just tupleType
  "Haskell.Prim.Tuple._×_×_" -> Just tupleType
  _ -> Nothing

tupleType' :: C Doc -> Term -> C [Term]
tupleType' err xs =
  reduce xs >>= \case
    Def q es
      | []    <- vis es, q ~~ "Agda.Builtin.Unit.⊤"     -> pure []
      | [_,_] <- vis es, q ~~ "Haskell.Prim.Tuple.Pair" -> pairToTuple es
    _ -> genericDocError =<< err
  where
    vis es = [ unArg a | Apply a <- es, visible a ]

    pairToTuple :: Elims -> C [Term]
    pairToTuple es
      | Just [x, xs] <- allApplyElims es = (unArg x:) <$> tupleType' err (unArg xs)
      | otherwise = genericDocError =<< text "Bad arguments for Pair: " <?> text (show es)

tupleType :: QName -> Elims -> C (Hs.Type ())
tupleType q es = do
  let err = sep [ prettyTCM (Def q es)
                , text "is not a concrete sequence of types."
                ]
  xs <- reduce (Def q es) >>= tupleType' err
  ts <- mapM compileType xs
  return $ Hs.TyTuple () Hs.Boxed ts

constrainType :: Hs.Asst () -> Hs.Type () -> Hs.Type ()
constrainType c = \case
  Hs.TyForall _ as (Just (Hs.CxTuple _ cs)) t -> Hs.TyForall () as (Just (Hs.CxTuple () (c:cs))) t
  Hs.TyForall _ as (Just (Hs.CxSingle _ c')) t -> Hs.TyForall () as (Just (Hs.CxTuple () [c,c'])) t
  Hs.TyForall _ as _ t -> Hs.TyForall () as (Just (Hs.CxSingle () c)) t
  t -> Hs.TyForall () Nothing (Just (Hs.CxSingle () c)) t

qualifyType :: String -> Hs.Type () -> Hs.Type ()
qualifyType s = \case
    Hs.TyForall _ (Just as) cs t -> Hs.TyForall () (Just (a:as)) cs t
    Hs.TyForall _ Nothing cs t -> Hs.TyForall () (Just [a]) cs t
    t -> Hs.TyForall () (Just [a]) Nothing t
  where
    a = Hs.UnkindedVar () $ Hs.Ident () s

-- Compile a top-level type that binds the current module parameters
-- (if any) as explicitly bound type arguments.
-- The continuation is called in an extended context with these type
-- arguments bound.
compileTopLevelType :: Type -> (Hs.Type () -> C a) -> C a
compileTopLevelType t cont = do
    ctxArgs <- getContextArgs
    modTel <- lookupSection =<< currentModule
    go (modTel `apply` ctxArgs) cont
  where
    go :: Telescope -> (Hs.Type () -> C a) -> C a
    go EmptyTel cont = do
      ctxArgs <- getContextArgs
      ty <- compileType . unEl =<< t `piApplyM` ctxArgs
      cont ty
    go (ExtendTel a atel) cont
      | isInstance a = do
          c <- Hs.TypeA () <$> compileType (unEl $ unDom a)
          underAbstraction a atel $ \tel ->
            go tel (cont . constrainType c)
      | otherwise = underAbstraction a atel $ \tel -> do
          unlessM (asks isCompilingInstance) $
            tellExtension Hs.ScopedTypeVariables
          go tel (cont . qualifyType (absName atel))

compileType' :: Term -> C (Strictness, Hs.Type ())
compileType' t = do
  s <- case t of
    Def f es -> fromMaybe Lazy <$> isUnboxRecord f
    _        -> return Lazy
  (s,) <$> compileType t

compileType :: Term -> C (Hs.Type ())
compileType t = do
  case t of
    Pi a b -> compileDom (absName b) a >>= \case
      DomType _ hsA -> do
        hsB <- underAbstraction a b $ compileType . unEl
        return $ Hs.TyFun () hsA hsB
      DomConstraint hsA -> do
        hsB <- underAbstraction a b (compileType . unEl)
        return $ constrainType hsA hsB
      DomDropped -> underAbstr a b (compileType . unEl)
    Def f es
      | Just semantics <- isSpecialType f -> setCurrentRange f $ semantics f es
      | Just args <- allApplyElims es ->
        ifJustM (isUnboxRecord f) (\_ -> compileUnboxType f args) $
        ifM (isTransparentFunction f) (compileTransparentType args) $ do
          vs <- compileTypeArgs args
          f <- compileQName f
          return $ tApp (Hs.TyCon () f) vs
    Var x es | Just args <- allApplyElims es -> do
      vs <- compileTypeArgs args
      x  <- hsName <$> compileVar x
      return $ tApp (Hs.TyVar () x) vs
    Sort s -> return (Hs.TyStar ())
    t -> genericDocError =<< text "Bad Haskell type:" <?> prettyTCM t

compileTypeArgs :: Args -> C [Hs.Type ()]
compileTypeArgs args = mapM (compileType . unArg) $ filter keepArg args

compileUnboxType :: QName -> Args -> C (Hs.Type ())
compileUnboxType r pars = do
  def <- theDef <$> getConstInfo r
  case recTel def `apply` pars of
    EmptyTel        -> __IMPOSSIBLE__
    (ExtendTel a _) -> compileType $ unEl $ unDom a

compileTransparentType :: Args -> C (Hs.Type ())
compileTransparentType args = compileTypeArgs args >>= \case
  [] -> genericError "Not supported: underapplied type synonyms"
  (v:vs) -> return $ v `tApp` vs

compileDom :: ArgName -> Dom Type -> C CompiledDom
compileDom x a
  | usableModality a = case getHiding a of
      Instance{} -> DomConstraint . Hs.TypeA () <$> compileType (unEl $ unDom a)
      NotHidden  -> uncurry DomType <$> compileType' (unEl $ unDom a)
      Hidden     -> do
        ifM (canErase $ unDom a)
            (return DomDropped)
            (genericDocError =<< do text "Implicit type argument not supported: " <+> prettyTCM x)
  | otherwise    = return DomDropped

compileTeleBinds :: Telescope -> C [Hs.TyVarBind ()]
compileTeleBinds tel =
  forM
    (mapMaybe
      (fmap unArgDom . checkArgDom)
      (teleArgNames tel `zip` flattenTel @Type tel))
    (uncurry compileKeptTeleBind)
  where
    checkArgDom (argName, argDom) | keepArg argName = Just (argName, argDom)
    checkArgDom _ | otherwise = Nothing

    unArgDom (argName, argDom) = (hsName . unArg $ argName, unDom argDom)

compileKeptTeleBind :: Hs.Name () -> Type -> C (Hs.TyVarBind ())
compileKeptTeleBind x t = do
  checkValidTyVarName x
  k <- compileKind t
  case k of
    Hs.TyStar _ ->
      -- TyStar is Haskell's default kind annotation
      return $ Hs.UnkindedVar () x
    _ -> genericDocError =<< do
      text "Kind of bound argument not supported:" <+>
        parens (text (Hs.prettyPrint x) <> text " : " <> prettyTCM t)

compileKind :: Type -> C (Hs.Kind ())
compileKind t = case unEl t of
  Sort (Type _) -> return (Hs.TyStar ())
  _ -> genericDocError =<< do
    text "Kind not supported:" <+> prettyTCM t
