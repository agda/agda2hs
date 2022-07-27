module Agda2Hs.Compile.Type where

import Control.Arrow ( (>>>), (***), (&&&), first, second )
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader

import Data.Generics ( mkT, everywhere, listify, extT, everything, mkQ, Data )
import Data.List
import Data.List.NonEmpty ( NonEmpty(..) )
import Data.Maybe
import Data.Map ( Map )
import qualified Data.Text as Text
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap

import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Build as Hs
import qualified Language.Haskell.Exts.Parser as Hs
import qualified Language.Haskell.Exts.Extension as Hs

import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.BasicOps

import Agda.Syntax.Common hiding ( Ranged )
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad hiding ( withCurrentModule )

import Agda.TypeChecking.CheckInternal ( infer )
import Agda.TypeChecking.Constraints ( noConstraints )
import Agda.TypeChecking.Conversion ( equalTerm )
import Agda.TypeChecking.InstanceArguments ( findInstance )
import Agda.TypeChecking.Level ( isLevelType )
import Agda.TypeChecking.MetaVars ( newInstanceMeta )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce ( instantiate, reduce )
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Records
import Agda.TypeChecking.Sort ( ifIsSort )

import Agda.Utils.Lens
import Agda.Utils.Pretty ( prettyShow )
import qualified Agda.Utils.Pretty as P
import Agda.Utils.List
import Agda.Utils.Impossible
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Functor

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils
import Agda2Hs.Pragma

isSpecialType :: QName -> Maybe (QName -> Elims -> C (Hs.Type ()))
isSpecialType = prettyShow >>> \ case
  "Haskell.Prim.Tuple.Tuple" -> Just tupleType
  "Haskell.Prim.Tuple._×_"   -> Just tupleType'
  "Haskell.Prim.Tuple._×_×_" -> Just tupleType'
  _ -> Nothing

tupleType' :: QName -> Elims -> C (Hs.Type ())
tupleType' q es = do
  Def tup es' <- reduce (Def q es)
  tupleType tup es'

tupleType :: QName -> Elims -> C (Hs.Type ())
tupleType _ es | Just [as] <- allApplyElims es = do
  let err = sep [ text "Argument"
                , nest 2 $ prettyTCM as
                , text "to Tuple is not a concrete list" ]
  xs <- makeList err (unArg as)
  ts <- mapM compileType xs
  return $ Hs.TyTuple () Hs.Boxed ts
tupleType _ es =
  genericDocError =<< text "Bad tuple arguments: " <?> prettyTCM es

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
      | Just args <- allApplyElims es -> do
        vs <- mapM (compileType . unArg) $ filter keepArg args
        f <- hsQName f
        return $ tApp (Hs.TyCon () f) vs
    Var x es | Just args <- allApplyElims es -> do
      vs <- mapM (compileType . unArg) $ filter keepArg args
      x  <- hsName <$> showTCM (Var x [])
      return $ tApp (Hs.TyVar () x) vs
    Sort s -> return (Hs.TyStar ())
    t -> genericDocError =<< text "Bad Haskell type:" <?> prettyTCM t

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
