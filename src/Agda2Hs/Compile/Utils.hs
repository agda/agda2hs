module Agda2Hs.Compile.Utils where

import Control.Monad ( forM_ )
import Control.Arrow ( Arrow((***)), (&&&) )
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer ( tell )
import Control.Monad.State ( put, modify )

import Data.List ( isPrefixOf, stripPrefix )
import Data.Maybe ( isJust )
import qualified Data.Map as M
import Data.String ( IsString(..) )

import GHC.Stack (HasCallStack)

import Agda.Compiler.Backend hiding ( Args )
import Agda.Interaction.BasicOps ( parseName )

import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Internal
import Agda.Syntax.Position ( noRange )
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad ( bindVariable, freshConcreteName, isDatatypeModule, resolveName )
import Agda.Syntax.Common.Pretty ( prettyShow )
import qualified Agda.Syntax.Common.Pretty as P

import Agda.TypeChecking.CheckInternal ( infer )
import Agda.TypeChecking.Constraints ( noConstraints )
import Agda.TypeChecking.Conversion ( equalTerm )
import Agda.TypeChecking.InstanceArguments ( findInstance )
import Agda.TypeChecking.Level ( isLevelType )
import Agda.TypeChecking.MetaVars ( newInstanceMeta )
import Agda.TypeChecking.Monad.SizedTypes ( isSizeType )
import Agda.TypeChecking.Pretty ( Doc, (<+>), text, PrettyTCM(..), pretty )
import Agda.TypeChecking.Records ( isRecordConstructor, getRecordOfField )
import Agda.TypeChecking.Reduce ( instantiate, reduce )
import Agda.TypeChecking.Substitute ( Subst, TelV(TelV), Apply(..) )
import Agda.TypeChecking.Telescope ( telView )

import Agda.Utils.Lens ( (<&>) )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Singleton
import Agda.Utils.Tuple ( (-*-) )

import AgdaInternals
import Agda2Hs.AgdaUtils ( (~~) )
import Agda2Hs.Compile.Types
import Agda2Hs.Pragma
import qualified Data.List as L
import Agda.Utils.Impossible ( __IMPOSSIBLE__ )

import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils
  ( Strictness(..), validVarName, validTypeName, validConName, hsName, pp )

agda2hsError :: (HasCallStack, MonadTCError m) => Doc -> m a
agda2hsError msg = typeError $ CustomBackendError "agda2hs" msg

agda2hsErrorM :: (HasCallStack, MonadTCError m) => m Doc -> m a
agda2hsErrorM msg = agda2hsError =<< msg

agda2hsStringError :: (HasCallStack, MonadTCError m) => String -> m a
agda2hsStringError = agda2hsError . fromString


data HsModuleKind
  = PrimModule
  | HsModule
  | AgdaModule
  deriving (Eq)

-- | Primitive modules provided by the agda2hs library.
-- None of those (and none of their children) will get processed.
primModules =
  [ "Agda.Builtin"
  , "Agda.Primitive"
  , "Haskell.Prim"
  , "Haskell.Prelude"
  ]

hsModuleKind :: Hs.ModuleName () -> HsModuleKind
hsModuleKind mod
  | any (`isPrefixOf` pp mod) primModules = PrimModule
  | "Haskell." `isPrefixOf` pp mod        = HsModule
  | otherwise                             = AgdaModule

dropHaskellPrefix :: Hs.ModuleName () -> Hs.ModuleName ()
dropHaskellPrefix (Hs.ModuleName l s) =
  Hs.ModuleName l $ fromMaybe s $ stripPrefix "Haskell." s

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
  let freshName = L.uncons $ filter (isFresh scope ctxNames) $ s : map (\i -> s ++ show i) [0..]
  return (maybe __IMPOSSIBLE__ fst freshName)
  where
    dummyName s = C.QName $ C.Name noRange C.NotInScope $ singleton $ C.Id s
    isFresh scope ctxNames s =
      null (scopeLookup (dummyName s) scope :: [AbstractName]) &&
      notElem s ctxNames

makeList :: C Doc -> Term -> C [Term]
makeList = makeList' "Agda.Builtin.List.List.[]" "Agda.Builtin.List.List._∷_"

makeList' :: String -> String -> C Doc -> Term -> C [Term]
makeList' nil cons err v = do
  v <- reduce v
  case v of
    Con c _ es
      | []      <- vis es, conName c ~~ nil  -> return []
      | [x, xs] <- vis es, conName c ~~ cons -> (x :) <$> makeList' nil cons err xs
    _ -> agda2hsErrorM err
  where
    vis es = [ unArg a | Apply a <- es, visible a ]

makeListP' :: String -> String -> C Doc -> DeBruijnPattern -> C [DeBruijnPattern]
makeListP' nil cons err p = do
  case p of
    ConP c _ ps
      | []      <- vis ps, conName c ~~ nil  -> return []
      | [x, xs] <- vis ps, conName c ~~ cons -> (x :) <$> makeListP' nil cons err xs
    _ -> agda2hsErrorM err
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

isPropSort :: Sort -> C Bool
isPropSort s = reduce s <&> \case
  Prop _ -> True
  _      -> False


-- Determine whether it is ok to erase arguments of this type,
-- even in the absence of an erasure annotation.
canErase :: Type -> C Bool
canErase a = do
  TelV tel b <- telView a
  addContext tel $ orM
    [ isErasedBaseType (unEl b)
    , isPropSort (getSort b)            -- _ : Prop
    ]

isErasedBaseType :: Term -> C Bool
isErasedBaseType x = orM
  [ isLevelType b                       -- Level
  , isJust <$> isSizeType b             -- Size
  ]
  where b = El __DUMMY_SORT__ x

hasCompilePragma :: QName -> C Bool
hasCompilePragma q = processPragma q <&> \case
  NoPragma{} -> False
  InlinePragma{} -> True
  DefaultPragma{} -> True
  ClassPragma{} -> True
  ExistingClassPragma{} -> True
  UnboxPragma{} -> True
  TransparentPragma{} -> True
  NewTypePragma{} -> True
  DerivePragma{} -> True

-- Exploits the fact that the name of the record type and the name of the record module are the
-- same, including the unique name ids.
isClassFunction :: QName -> C Bool
isClassFunction = isClassModule . qnameModule

isClassModule :: ModuleName -> C Bool
isClassModule m
  | null $ mnameToList m = return False
  | otherwise            = do
    minRec <- asks minRecordName
    if Just m == minRec then return True else isClassName (mnameToQName m)

-- | Check if the given name corresponds to a type class in Haskell.
isClassName :: QName -> C Bool
isClassName q = getConstInfo' q >>= \case
  Right Defn{defName = r, theDef = Record{}} ->
    -- It would be nicer if we remembered this from when we looked at the record the first time.
    processPragma r <&> \case
      ClassPragma _       -> True
      ExistingClassPragma -> True
      _                   -> False
  _                       -> return False

-- | Check if the given type corresponds to a class constraint in Haskell.
isClassType :: Type -> C Bool
isClassType a = do
  TelV _ t <- telView a
  case unEl t of
    Def cl _ -> isClassName cl
    _        -> return False

-- Drops the last (record) module for typeclass methods
dropClassModule :: ModuleName -> C ModuleName
dropClassModule m@(MName ns) = isClassModule m >>= \case
  True  -> dropClassModule $ MName $ init ns
  False -> return m

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

isTupleRecord :: QName -> C (Maybe Hs.Boxed)
isTupleRecord q = do
  getConstInfo q >>= \case
    Defn{defName = r, theDef = Record{}} ->
      processPragma r <&> \case
        TuplePragma b -> Just b
        _             -> Nothing
    _ -> return Nothing

isTupleConstructor :: QName -> C (Maybe Hs.Boxed)
isTupleConstructor q =
  caseMaybeM (isRecordConstructor q) (return Nothing) $ isTupleRecord . fst

isTupleProjection :: QName -> C (Maybe Hs.Boxed)
isTupleProjection q =
  caseMaybeM (liftTCM $ getRecordOfField q) (return Nothing) isTupleRecord

isTransparentFunction :: QName -> C Bool
isTransparentFunction q = do
  getConstInfo q >>= \case
    Defn{defName = r, theDef = Function{}} ->
      (TransparentPragma ==) <$> processPragma r
    _ -> return False

isInlinedFunction :: QName -> C Bool
isInlinedFunction q = do
  getConstInfo q >>= \case
    Defn{defName = r, theDef = Function{}} ->
      (InlinePragma ==) <$> processPragma r
    _ -> return False

withNestedType :: C a -> C a
withNestedType = local $ \e -> e { isNestedInType = True }

compileLocal :: C a -> C a
compileLocal = local $ \e -> e { compilingLocal = True }

addWhereModule :: ModuleName  -> C a -> C a
addWhereModule mName = local $ \e -> e { whereModules = mName : whereModules e }

modifyLCase :: (Int -> Int) -> CompileState -> CompileState
modifyLCase f (CompileState {lcaseUsed = n}) = CompileState {lcaseUsed = f n}

incrementLCase, decrementLCase :: C ()
incrementLCase = modify $ modifyLCase (+ 1)
decrementLCase = modify $ modifyLCase (\n -> n - 1)

-- Always construct lambda cases with this function.
hsLCase :: [Hs.Alt ()] -> C (Hs.Exp ())
hsLCase = (incrementLCase >>) . return . Hs.LCase ()

ensureNoLocals :: String -> C ()
ensureNoLocals msg = unlessM (null <$> asks locals) $ agda2hsStringError msg

withLocals :: LocalDecls -> C a -> C a
withLocals ls = local $ \e -> e { locals = ls }

checkValidVarName :: Hs.Name () -> C ()
checkValidVarName x = unless (validVarName x) $ agda2hsErrorM $ do
  text "Invalid name for Haskell variable: " <+> text (Hs.prettyPrint x)

checkValidTyVarName :: Hs.Name () -> C ()
checkValidTyVarName x = unless (validVarName x) $ agda2hsErrorM $ do
  text "Invalid name for Haskell type variable: " <+> text (Hs.prettyPrint x)

checkValidFunName :: Hs.Name () -> C ()
checkValidFunName x = unless (validVarName x) $ agda2hsErrorM $ do
  text "Invalid name for Haskell function: " <+> text (Hs.prettyPrint x)

checkValidTypeName :: Hs.Name () -> C ()
checkValidTypeName x = unless (validTypeName x) $ agda2hsErrorM $ do
  text "Invalid name for Haskell type: " <+> text (Hs.prettyPrint x)

checkValidConName :: Hs.Name () -> C ()
checkValidConName x = unless (validConName x) $ agda2hsErrorM $ do
  text "Invalid name for Haskell constructor: " <+> text (Hs.prettyPrint x)

tellImport :: Import -> C ()
tellImport imp = tell $ CompileOutput [imp] [] [] []

tellExtension :: Hs.KnownExtension -> C ()
tellExtension pr = tell $ CompileOutput [] [pr] [] []

tellNoErased :: String -> C ()
tellNoErased er = tell $ CompileOutput [] [] [er] []

tellAllCheckable :: QName -> C ()
tellAllCheckable chk = tell $ CompileOutput [] [] [] [chk]

tellUnboxedTuples :: Hs.Boxed -> C ()
tellUnboxedTuples Hs.Boxed = return ()
tellUnboxedTuples Hs.Unboxed = tellExtension $ Hs.UnboxedTuples

addPatBang :: Strictness -> Hs.Pat () -> C (Hs.Pat ())
addPatBang Strict p = tellExtension Hs.BangPatterns >>
  return (Hs.PBangPat () p)
addPatBang Lazy   p = return p

addTyBang :: Strictness -> Hs.Type () -> C (Hs.Type ())
addTyBang Strict ty = tellExtension Hs.BangPatterns >>
  return (Hs.TyBang () (Hs.BangedTy ()) (Hs.NoUnpackPragma ()) ty)
addTyBang Lazy   ty = return ty

checkSingleElement :: Hs.Name () -> [b] -> String -> C ()
checkSingleElement name fs s = unless (length fs == 1) $ agda2hsErrorM $ do
  text (s ++ ":") <+> text (Hs.prettyPrint name)

checkNewtypeCon :: Hs.Name () -> [b] -> C ()
checkNewtypeCon name tys =
  checkSingleElement name tys "Newtype must have exactly one field in constructor"

checkFixityLevel :: QName -> FixityLevel -> C (Maybe Int)
checkFixityLevel name Unrelated = pure Nothing
checkFixityLevel name (Related lvl) =
  if lvl /= fromInteger (round lvl) || lvl < 0
    then agda2hsErrorM $ text "Invalid fixity" <+> pretty lvl
                     <+> text "for operator"   <+> prettyTCM name
    else pure (Just (round lvl))

maybePrependFixity :: QName -> Fixity -> C RtcDecls -> C RtcDecls
maybePrependFixity n f comp | f /= noFixity = do
  hsLvl <- checkFixityLevel n (fixityLevel f)
  let x = hsName $ prettyShow $ qnameName n
  let hsAssoc = case fixityAssoc f of
        NonAssoc   -> Hs.AssocNone ()
        LeftAssoc  -> Hs.AssocLeft ()
        RightAssoc -> Hs.AssocRight ()
  let head = (Hs.InfixDecl () hsAssoc hsLvl [Hs.VarOp () x]:)
  (head <$>) <$> comp
maybePrependFixity n f comp = comp


checkNoAsPatterns :: DeBruijnPattern -> C ()
checkNoAsPatterns = \case
    VarP i _ -> checkPatternInfo i
    DotP i _ -> checkPatternInfo i
    ConP _ cpi ps -> do
      checkPatternInfo $ conPInfo cpi
      forM_ ps $ checkNoAsPatterns . namedArg
    LitP i _ -> checkPatternInfo i
    ProjP{} -> return ()
    IApplyP i _ _ _ -> checkPatternInfo i
    DefP i _ ps -> do
      checkPatternInfo i
      forM_ ps $ checkNoAsPatterns . namedArg
  where
    checkPatternInfo :: PatternInfo -> C ()
    checkPatternInfo i = unless (null $ patAsNames i) $
      agda2hsError "not supported: as patterns"

noWriteImports :: C a -> C a
noWriteImports = local $ \e -> e { writeImports = False }

testResolveStringName :: String -> C (Maybe QName)
testResolveStringName s = do
  cqname <- liftTCM $ parseName noRange s
  rname <- liftTCM $ resolveName cqname
  case rname of
    DefinedName _ aname _ -> return $ Just $ anameName aname
    _ -> return Nothing

resolveStringName :: String -> C QName
resolveStringName s = do
  testResolveStringName s >>= \case
    Just aname -> return aname
    Nothing -> genericDocError =<< text ("Couldn't find " ++ s)

-- Check if runtime checks should be emitted, i.e. the feature is
-- enabled and the name is not in the trusted computing base.
-- This is not included in RuntimeCheckUtils.hs for dependency reasons.
emitsRtc :: QName -> C Bool
emitsRtc qname = do
  topName <- prettyTCM $ List1.head $ mnameToList1 $ qnameModule qname
  asks $ (show topName /= "Haskell" &&) . rtc
