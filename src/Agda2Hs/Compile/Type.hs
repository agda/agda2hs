module Agda2Hs.Compile.Type where

import Control.Arrow ( (>>>) )

import qualified Language.Haskell.Exts.Syntax as Hs

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
import Agda.Utils.Monad ( forMaybeM, ifM )
import Agda.Utils.Size ( Sized(size) )
import Agda.Utils.Functor ( ($>) )

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name ( hsQName )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

isSpecialType :: QName -> Maybe (QName -> Elims -> C (Hs.Type ()))
isSpecialType = prettyShow >>> \ case
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

compileTopLevelType :: Type -> C (Hs.Type ())
compileTopLevelType t = do
  ctxArgs <- getContextArgs
  compileType . unEl =<< t `piApplyM` ctxArgs

compileType :: Term -> C (Hs.Type ())
compileType t = do
  case t of
    Pi a b -> compileDom (absName b) a >>= \case
      DomType hsA -> do
        hsB <- underAbstraction a b $ compileType . unEl
        return $ Hs.TyFun () hsA hsB
      DomConstraint hsA -> do
        hsB <- underAbstraction a b (compileType . unEl)
        return $ Hs.TyForall () Nothing (Just $ Hs.CxSingle () hsA) hsB
      DomDropped -> underAbstr a b (compileType . unEl)
    Def f es
      | Just semantics <- isSpecialType f -> setCurrentRange f $ semantics f es
      | Just args <- allApplyElims es ->
        ifM (isUnboxRecord f) (compileUnboxType f args) $ do
          vs <- mapM (compileType . unArg) $ filter keepArg args
          f <- hsQName f
          return $ tApp (Hs.TyCon () f) vs
    Var x es | Just args <- allApplyElims es -> do
      vs <- mapM (compileType . unArg) $ filter keepArg args
      x  <- hsName <$> showTCM (Var x [])
      return $ tApp (Hs.TyVar () x) vs
    Sort s -> return (Hs.TyStar ())
    t -> genericDocError =<< text "Bad Haskell type:" <?> prettyTCM t

compileUnboxType :: QName -> Args -> C (Hs.Type ())
compileUnboxType r pars = do
  def <- theDef <$> getConstInfo r
  case recTel def `apply` pars of
    EmptyTel        -> __IMPOSSIBLE__
    (ExtendTel a _) -> compileType $ unEl $ unDom a

compileDom :: ArgName -> Dom Type -> C CompiledDom
compileDom x a
  | usableModality a = case getHiding a of
      Instance{} -> DomConstraint . Hs.TypeA () <$> compileType (unEl $ unDom a)
      NotHidden  -> DomType <$> compileType (unEl $ unDom a)
      Hidden     -> do
        ifM (canErase $ unDom a)
            (return DomDropped)
            (genericDocError =<< do text "Implicit type argument not supported: " <+> prettyTCM x)
  | otherwise    = return DomDropped

compileTele :: Telescope -> C [Arg Term]
compileTele tel = addContext tel $ do
  forMaybeM (zip3 (downFrom $ size tel) (teleNames tel) (flattenTel tel)) $ \(i,x,a) -> do
    compileDom x a >>= \case
      DomType{}       -> return $ Just $ argFromDom a $> var i
      DomConstraint{} -> genericDocError =<< text "Not supported: type-level constraints"
      DomDropped{}    -> return Nothing
