module Agda2Hs.Compile.Utils where

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
import Agda2Hs.Compile.Types
import Agda2Hs.HsUtils
import Agda2Hs.Pragma

concatUnzip :: [([a], [b])] -> ([a], [b])
concatUnzip = (concat *** concat) . unzip

liftTCM1 :: (TCM a -> TCM b) -> C a -> C b
liftTCM1 k m = ReaderT (k . runReaderT m)

showTCM :: PrettyTCM a => a -> C String
showTCM x = lift $ show <$> prettyTCM x

isInScopeUnqualified :: QName -> C Bool
isInScopeUnqualified x = lift $ do
  ys <- inverseScopeLookupName' AmbiguousAnything x <$> getScope
  return $ any (not . C.isQualified) ys

freshString :: String -> C String
freshString s = liftTCM (freshName_ s) >>= showTCM

makeList :: C Doc -> Term -> C [Term]
makeList = makeList' "Agda.Builtin.List.List.[]" "Agda.Builtin.List.List._∷_"

makeList' :: String -> String -> C Doc -> Term -> C [Term]
makeList' nil cons err v = do
  v <- reduce v
  case v of
    Con c _ es
      | []      <- vis es, conName c ~~ nil  -> return []
      | [x, xs] <- vis es, conName c ~~ cons -> (x :) <$> makeList' nil cons err xs
    _ -> genericDocError =<< err
  where
    vis es = [ unArg a | Apply a <- es, visible a ]

makeListP' :: String -> String -> C Doc -> DeBruijnPattern -> C [DeBruijnPattern]
makeListP' nil cons err p = do
  case p of
    ConP c _ ps
      | []      <- vis ps, conName c ~~ nil  -> return []
      | [x, xs] <- vis ps, conName c ~~ cons -> (x :) <$> makeListP' nil cons err xs
    _ -> genericDocError =<< err
  where
    vis ps = [ namedArg p | p <- ps, visible p ]

-- When going under a binder we need to update the scope as well as the context in order to get
-- correct printing of variable names (Issue #14).
bindVar :: Int -> C ()
bindVar i = do
  x <- nameOfBV i
  liftTCM $ bindVariable LambdaBound (nameConcrete x) x

underAbstr  :: Subst a => Dom Type -> Abs a -> (a -> C b) -> C b
underAbstr a b ret
  | absName b == "_" = underAbstraction' KeepNames a b ret
  | otherwise        = underAbstraction' KeepNames a b $ \ body ->
                         liftTCM1 localScope $ bindVar 0 >> ret body

underAbstr_ :: Subst a => Abs a -> (a -> C b) -> C b
underAbstr_ = underAbstr __DUMMY_DOM__

-- Determine whether an argument should be kept or dropped.
-- We drop all arguments that have quantity 0 (= run-time erased).
-- We also drop hidden non-erased arguments (which should all be of
-- type Level or Set l).
keepArg :: (LensHiding a, LensModality a) => a -> Bool
keepArg x = usableModality x && visible x

-- Determine whether it is ok to erase arguments of this type,
-- even in the absence of an erasure annotation.
canErase :: Type -> C Bool
canErase a = do
  TelV tel b <- telView a
  addContext tel $
    isLevelType b `or2M` ((isJust . isSort) <$> reduce (unEl b))

-- Exploits the fact that the name of the record type and the name of the record module are the
-- same, including the unique name ids.
isClassFunction :: QName -> C Bool
isClassFunction q
  | null $ mnameToList m = return False
  | otherwise            = do
    minRec <- asks minRecordName
    getConstInfo' (mnameToQName m) >>= \ case
      _ | Just m == minRec -> return True
      Right Defn{defName = r, theDef = Record{}} ->
        -- It would be nicer if we remembered this from when we looked at the record the first time.
        processPragma r <&> \ case
          ClassPragma _       -> True
          ExistingClassPragma -> True
          _                   -> False
      _                             -> return False
  where
    m = qnameModule q

checkInstance :: Term -> C ()
checkInstance u | varOrDef u = liftTCM $ noConstraints $ do
  reportSDoc "agda2hs.checkInstance" 5 $ text "checkInstance" <+> prettyTCM u
  t <- infer u
  reportSDoc "agda2hs.checkInstance" 15 $ text "  inferred type:" <+> prettyTCM t
  (m, v) <- newInstanceMeta "" t
  reportSDoc "agda2hs.checkInstance" 15 $ text "  instance meta:" <+> prettyTCM m
  findInstance m Nothing
  reportSDoc "agda2hs.checkInstance" 15 $ text "  inferred instance:" <+> (prettyTCM =<< instantiate v)
  reportSDoc "agda2hs.checkInstance" 65 $ text "  inferred instance:" <+> (pure . P.pretty =<< instantiate v)
  reportSDoc "agda2hs.checkInstance" 65 $ text "  checking instance:" <+> (pure . P.pretty =<< instantiate u)
  equalTerm t u v `catchError` \_ ->
    genericDocError =<< text "illegal instance: " <+> prettyTCM u
  where
    varOrDef Var{} = True
    varOrDef Def{} = True
    varOrDef _     = False
-- We need to compile applications of `fromNat`, `fromNeg`, and
-- `fromString` where the constraint type is ⊤ or IsTrue .... Ideally
-- this constraint would be marked as erased but this would involve
-- changing Agda builtins.
checkInstance u@(Con c _ _)
  | prettyShow (conName c) == "Agda.Builtin.Unit.tt" ||
    prettyShow (conName c) == "Haskell.Prim.IsTrue.itsTrue" ||
    prettyShow (conName c) == "Haskell.Prim.IsFalse.itsFalse" = return ()
checkInstance u = genericDocError =<< text "illegal instance: " <+> prettyTCM u
