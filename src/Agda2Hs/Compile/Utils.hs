module Agda2Hs.Compile.Utils where

import Control.Arrow ( Arrow((***)) )
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer ( tell )
import Control.Monad.State ( put, modify )

import Data.Maybe ( isJust )
import qualified Data.Map as M

import qualified Language.Haskell.Exts as Hs

import Agda.Compiler.Backend hiding ( Args )

import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Internal
import Agda.Syntax.Position ( noRange )
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad ( bindVariable, freshConcreteName, isDatatypeModule )
import Agda.Syntax.Common.Pretty ( prettyShow )
import qualified Agda.Syntax.Common.Pretty as P

import Agda.TypeChecking.CheckInternal ( infer )
import Agda.TypeChecking.Constraints ( noConstraints )
import Agda.TypeChecking.Conversion ( equalTerm )
import Agda.TypeChecking.InstanceArguments ( findInstance )
import Agda.TypeChecking.Level ( isLevelType )
import Agda.TypeChecking.MetaVars ( newInstanceMeta )
import Agda.TypeChecking.Monad.SizedTypes ( isSizeType )
import Agda.TypeChecking.Pretty ( Doc, (<+>), text, PrettyTCM(..) )
import Agda.TypeChecking.Records ( isRecordConstructor, getRecordOfField )
import Agda.TypeChecking.Reduce ( instantiate, reduce )
import Agda.TypeChecking.Substitute ( Subst, TelV(TelV), Apply(..) )
import Agda.TypeChecking.Telescope ( telView )

import Agda.Utils.Lens ( (<&>) )
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Singleton

import AgdaInternals
import Agda2Hs.AgdaUtils ( (~~) )
import Agda2Hs.Compile.Types
import Agda2Hs.HsUtils
import Agda2Hs.Pragma

concatUnzip :: [([a], [b])] -> ([a], [b])
concatUnzip = (concat *** concat) . unzip

infixr 0 /\, \/
(/\), (\/) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
f /\ g = \x -> f x && g x
f \/ g = \x -> f x || g x

showTCM :: PrettyTCM a => a -> C String
showTCM x = liftTCM $ show <$> prettyTCM x

setCurrentRangeQ :: QName -> C a -> C a
setCurrentRangeQ = setCurrentRange . nameBindingSite . qnameName

isInScopeUnqualified :: QName -> C Bool
isInScopeUnqualified x = lift $ do
  ys <- inverseScopeLookupName' AmbiguousAnything x <$> getScope
  return $ any (not . C.isQualified) ys

freshString :: String -> C String
freshString s = liftTCM $ do
  scope <- getScope
  ctxNames <- map (prettyShow . nameConcrete) <$> getContextNames
  return $ head $ filter (isFresh scope ctxNames) $ s : map (\i -> s ++ show i) [0..]
  where
    dummyName s = C.QName $ C.Name noRange C.NotInScope $ singleton $ C.Id s
    isFresh scope ctxNames s =
      null (scopeLookup (dummyName s) scope :: [AbstractName]) &&
      not (s `elem` ctxNames)

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
underAbstr = underAbstraction' KeepNames

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
  addContext tel $ orM
    [ isLevelType b
    , isJust <$> isSizeType b
    , ((isJust . isSort) <$> reduce (unEl b))
    ]

-- Exploits the fact that the name of the record type and the name of the record module are the
-- same, including the unique name ids.
isClassFunction :: QName -> C Bool
isClassFunction = isClassModule . qnameModule

isClassModule :: ModuleName -> C Bool
isClassModule m
  | null $ mnameToList m = return False
  | otherwise            = do
    minRec <- asks minRecordName
    getConstInfo' (mnameToQName m) >>= \case
      _ | Just m == minRec -> return True
      Right Defn{defName = r, theDef = Record{}} ->
        -- It would be nicer if we remembered this from when we looked at the record the first time.
        processPragma r <&> \case
          ClassPragma _       -> True
          ExistingClassPragma -> True
          _                   -> False
      _                             -> return False

-- Drops the last (record) module for typeclass methods
dropClassModule :: ModuleName -> C ModuleName
dropClassModule m@(MName ns) = isClassModule m >>= \case
  True  -> dropClassModule $ MName $ init ns
  False -> return m

moduleParametersToDrop :: ModuleName -> C Telescope
moduleParametersToDrop mod = do
   reportSDoc "agda2hs.moduleParameters" 25 $ text "Getting telescope for" <+> prettyTCM mod
   isDatatypeModule mod >>= \case
     Just _ -> return EmptyTel
     Nothing -> do
       reportSDoc "agda2hs.moduleParameters" 25 $ text "Current context: " <+> (prettyTCM =<< getContext)
       ctxArgs <- getContextArgs
       reportSDoc "agda2hs.moduleParameters" 25 $ text "Context arguments: " <+> prettyTCM ctxArgs
       sec <- lookupSection mod
       reportSDoc "agda2hs.moduleParameters" 25 $ text "Module section: " <+> prettyTCM sec
       return $ sec `apply` ctxArgs

isUnboxRecord :: QName -> C (Maybe Strictness)
isUnboxRecord q = do
  getConstInfo q >>= \case
    Defn{defName = r, theDef = Record{}} ->
      processPragma r <&> \case
        UnboxPragma s -> Just s
        _             -> Nothing
    _ -> return Nothing

isUnboxConstructor :: QName -> C (Maybe Strictness)
isUnboxConstructor q =
  caseMaybeM (isRecordConstructor q) (return Nothing) $ isUnboxRecord . fst

isUnboxProjection :: QName -> C (Maybe Strictness)
isUnboxProjection q =
  caseMaybeM (liftTCM $ getRecordOfField q) (return Nothing) isUnboxRecord

isTransparentFunction :: QName -> C Bool
isTransparentFunction q = do
  getConstInfo q >>= \case
    Defn{defName = r, theDef = Function{}} ->
      processPragma r <&> \case
        TransparentPragma -> True
        _                 -> False
    _ -> return False

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

modifyLCase :: (Int -> Int) -> CompileState -> CompileState
modifyLCase f (CompileState {lcaseUsed = n}) = CompileState {lcaseUsed = f n}

incrementLCase, decrementLCase :: C ()
incrementLCase = modify $ modifyLCase (+ 1)
decrementLCase = modify $ modifyLCase (\n -> n - 1)

-- Always construct lambda cases with this function.
hsLCase :: [Hs.Alt ()] -> C (Hs.Exp ())
hsLCase = (incrementLCase >>) . return . Hs.LCase ()

ensureNoLocals :: String -> C ()
ensureNoLocals msg = unlessM (null <$> asks locals) $ genericError msg

withLocals :: LocalDecls -> C a -> C a
withLocals ls = local $ \e -> e { locals = ls }

checkValidVarName :: Hs.Name () -> C ()
checkValidVarName x = unless (validVarName x) $ genericDocError =<< do
  text "Invalid name for Haskell variable: " <+> text (Hs.prettyPrint x)

checkValidTyVarName :: Hs.Name () -> C ()
checkValidTyVarName x = unless (validVarName x) $ genericDocError =<< do
  text "Invalid name for Haskell type variable: " <+> text (Hs.prettyPrint x)

checkValidFunName :: Hs.Name () -> C ()
checkValidFunName x = unless (validVarName x) $ genericDocError =<< do
  text "Invalid name for Haskell function: " <+> text (Hs.prettyPrint x)

checkValidTypeName :: Hs.Name () -> C ()
checkValidTypeName x = unless (validTypeName x) $ genericDocError =<< do
  text "Invalid name for Haskell type: " <+> text (Hs.prettyPrint x)

checkValidConName :: Hs.Name () -> C ()
checkValidConName x = unless (validConName x) $ genericDocError =<< do
  text "Invalid name for Haskell constructor: " <+> text (Hs.prettyPrint x)

tellImport :: Import -> C ()
tellImport imp = tell $ CompileOutput [imp] []

tellExtension :: Hs.KnownExtension -> C ()
tellExtension pr = tell $ CompileOutput [] [pr]

addPatBang :: Strictness -> Hs.Pat () -> C (Hs.Pat ())
addPatBang Strict p = tellExtension Hs.BangPatterns >>
  return (Hs.PBangPat () p)
addPatBang Lazy   p = return p

addTyBang :: Strictness -> Hs.Type () -> C (Hs.Type ())
addTyBang Strict ty = tellExtension Hs.BangPatterns >>
  return (Hs.TyBang () (Hs.BangedTy ()) (Hs.NoUnpackPragma ()) ty)
addTyBang Lazy   ty = return ty

checkSingleElement :: Hs.Name () -> [b] -> String -> C ()
checkSingleElement name fs s = unless (length fs == 1) $ genericDocError =<< do
  text (s ++ ":") <+> text (Hs.prettyPrint name)

checkingVars :: C a -> C a
checkingVars = local $ \e -> e { checkVar = True }
