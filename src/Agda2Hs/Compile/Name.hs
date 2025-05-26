module Agda2Hs.Compile.Name where

import Control.Arrow ( (>>>) )
import Control.Applicative ( (<|>) )
import Control.Monad
import Control.Monad.Except ( catchError )
import Control.Monad.Reader

import Data.Functor ( (<&>) )
import Data.Bifunctor ( bimap )
import Data.List ( intercalate, isPrefixOf, stripPrefix )
import Data.Text ( unpack )
import qualified Data.Map.Strict as Map

import qualified Language.Haskell.Exts.Pretty as Hs
import qualified Language.Haskell.Exts.Syntax as Hs

import Agda.Compiler.Backend hiding ( topLevelModuleName )
import Agda.Compiler.Common ( topLevelModuleName )

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common hiding (Rewrite)
import Agda.Syntax.Internal
import Agda.Syntax.Position
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Scope.Base ( inverseScopeLookupName, amodName )
import Agda.Syntax.Scope.Monad ( resolveName, isDatatypeModule )
import Agda.Syntax.TopLevelModuleName
import Agda.Syntax.Common.Pretty ( prettyShow )
import qualified Agda.Syntax.Common.Pretty as P

import Agda.TypeChecking.Datatypes ( isDataOrRecordType )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records ( isRecordConstructor )
import Agda.TypeChecking.Warnings ( warning )

import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe ( isJust, isNothing, whenJust, fromMaybe, caseMaybeM )
import Agda.Utils.Monad ( orM, whenM )

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils


isSpecialCon :: QName -> Maybe (Hs.QName ())
isSpecialCon = prettyShow >>> \case
    "Agda.Builtin.List.List"     -> special Hs.ListCon
    "Agda.Builtin.List.List._∷_" -> special Hs.Cons
    "Agda.Builtin.List.List.[]"  -> special Hs.ListCon
    "Agda.Builtin.Unit.⊤"        -> special Hs.UnitCon
    "Agda.Builtin.Unit.tt"       -> special Hs.UnitCon
    _ -> Nothing
  where special c = Just (Hs.Special () $ c ())

-- | Convert identifier and import module strings into the Haskell equivalent syntax.
toNameImport :: String -> Maybe String -> (Hs.Name (), Maybe Import)
toNameImport x Nothing = (hsName x, Nothing)
toNameImport x (Just mod) =
  ( hsName x
  , Just $ Import (hsModuleName mod) Unqualified Nothing (hsName x) (Hs.NoNamespace ())
  )

-- | Default rewrite rules.
defaultSpecialRules :: SpecialRules
defaultSpecialRules = Map.fromList
  [ "Agda.Builtin.Nat.Nat"          `to` "Natural"      `importing` Just "Numeric.Natural"
  , "Haskell.Prelude.coerce"        `to` "unsafeCoerce" `importing` Just "Unsafe.Coerce"
  , "Agda.Builtin.Int.Int"          `to` "Integer"      `importing` Nothing
  , "Agda.Builtin.Word.Word64"      `to` "Word"         `importing` Nothing
  , "Agda.Builtin.Float.Float"      `to` "Double"       `importing` Nothing
  , "Agda.Builtin.Bool.Bool.false"  `to` "False"        `importing` Nothing
  , "Agda.Builtin.Bool.Bool.true"   `to` "True"         `importing` Nothing
  , "Haskell.Prim._∘_"              `to` "_._"          `importing` Nothing
  , "Haskell.Prim.Monad.Dont._>>=_" `to` "_>>=_"        `importing` Nothing
  , "Haskell.Prim.Monad.Dont._>>_"  `to` "_>>_"         `importing` Nothing
  , "Haskell.Prim.Tuple.first"      `to` "first"        `importing` Just "Control.Arrow"
  , "Haskell.Prim.Tuple.second"     `to` "second"       `importing` Just "Control.Arrow"
  , "Haskell.Prim.Tuple._***_"      `to` "_***_"        `importing` Just "Control.Arrow"
  ]
  where infixr 6 `to`, `importing`
        to = (,)
        importing = toNameImport

-- | Check whether the given name should be rewritten to a special Haskell name, possibly with new imports.
isSpecialName :: QName -> C (Maybe (Hs.Name (), Maybe Import))
isSpecialName f = asks (Map.lookup (prettyShow f) . rewrites)

compileName :: Applicative m => Name -> m (Hs.Name ())
compileName n = hsName . show <$> pretty (nameConcrete n)

compileQName :: QName -> C (Hs.QName ())
compileQName f
  | Just c <- isSpecialCon f
  = do
    reportSDoc "agda2hs.name" 25 $ text $
      "compiling name: " ++ prettyShow f ++
      " to special constructor: " ++ Hs.prettyPrint c
    return c
  | otherwise = do
    f <- isRecordConstructor f >>= return . \case
      Just (r, def) | not (_recNamedCon def) -> r -- use record name for unnamed constructors
      _                                      -> f
    hf0 <- compileName (qnameName f)
    special <- isSpecialName f
    let (hf, mimpBuiltin) = fromMaybe (hf0, Nothing) special

    parent <- parentName f
    par <- traverse (compileName . qnameName) parent
    let mod0 = qnameModule $ fromMaybe f parent
    (mkind, mod) <- compileModuleName mod0

    existsInHaskell <- orM
      [ pure $ isJust special
      , pure $ mkind == PrimModule
      , pure $ mkind == HsModule
      , hasCompilePragma f
      , isClassFunction f
      , isWhereFunction f
      , maybe (pure False) hasCompilePragma parent
      ]

    unless existsInHaskell $ do
      reportSDoc "agda2hs.name" 20 $ text "DOES NOT EXIST IN HASKELL"
      typeError $ CustomBackendError "agda2hs" $ P.text $
        "Symbol " ++ Hs.prettyPrint hf ++ " is missing a COMPILE pragma or rewrite rule"

    currMod <- hsTopLevelModuleName <$> asks currModule
    let skipModule = mod == currMod
                  || isJust mimpBuiltin
                  || prettyShow mod0 `elem` primMonadModules
    qual <- if | skipModule -> return Unqualified
               | otherwise  -> getQualifier (fromMaybe f parent) mod
    -- we only calculate this when dealing with type operators; usually that's where 'type' prefixes are needed in imports
    namespace <- (case hf of
          Hs.Symbol _ _ -> getNamespace f
          Hs.Ident  _ _ -> return (Hs.NoNamespace ()))
    let
      -- We don't generate "import Prelude" for primitive modules,
      -- unless a name is qualified.
      mimp = if mkind /= PrimModule || isQualified qual
             then Just (Import mod qual par hf namespace)
             else Nothing
      qf = qualify mod hf qual

    -- add (possibly qualified) import
    whenM (asks writeImports) $
      whenJust (mimpBuiltin <|> mimp) tellImport

    reportSDoc "agda2hs.name" 25 $ text
       $ "-------------------------------------------------"
      ++ "\ncompiling name: " ++ prettyShow f
      ++ "\nhaskell name: " ++ Hs.prettyPrint hf
      ++ "\nparent name: " ++ prettyShow parent
      ++ "\nmod0: " ++ prettyShow mod0
      ++ "\nmodule name: " ++ Hs.prettyPrint mod
      ++ "\ncurrent module: " ++ Hs.prettyPrint currMod
      ++ "\nqualifier: " ++ prettyShow (fmap (fmap pp) qual)
      ++ "\n(qualified) haskell name: " ++ pp qf
    return qf
  where
    parentName :: QName -> C (Maybe QName)
    parentName q = (theDef <$> getConstInfo q) >>= return . \case
      Constructor {conData = dt} -> Just dt
      Function {funProjection = proj}
        | Right (Projection {projProper = Just{}, projFromType = rt}) <- proj
        -> Just $ unArg rt
      _ -> Nothing

    getQualifier :: QName -> Hs.ModuleName () -> C Qualifier
    getQualifier f mod =
      (inverseScopeLookupName f <$> getScope) >>= \case
        (C.QName{} : _) -> return Unqualified
        (C.Qual as C.QName{} : _) -> liftTCM $ do
          let qual = hsModuleName $ prettyShow as
          lookupModuleInCurrentModule as >>= \case
            (x:_) | qual /= mod -> do
              isDataMod <- isJust <$> isDatatypeModule (amodName x)
              return $ QualifiedAs (if isDataMod then Nothing else Just qual)
            _ -> return $ QualifiedAs Nothing
          `catchError` \_ -> return $ QualifiedAs Nothing
        _ -> return $ QualifiedAs Nothing

    qualify :: Hs.ModuleName () -> Hs.Name () -> Qualifier -> Hs.QName ()
    qualify mod n = \case
      (QualifiedAs as) -> Hs.Qual () (fromMaybe mod as) n
      Unqualified      -> Hs.UnQual () n

    primMonadModules = ["Haskell.Prim.Monad.Dont", "Haskell.Prim.Monad.Do"]

    -- Determine whether it is a type operator or an "ordinary" operator.
    -- _getSort is not for that; e. g. a data has the same sort as its constructor.
    getNamespace :: QName -> C (Hs.Namespace ())
    getNamespace qName = do
      definition <- getConstInfo qName
      case isSort $ unEl $ getResultType $ defType definition of
        Just _         -> (reportSDoc "agda2hs.name" 25 $ text $ (prettyShow $ nameCanonical $ qnameName f)
                                              ++ " is a type operator; will add \"type\" prefix before it") >>
                          return (Hs.TypeNamespace ())
        _              -> return (Hs.NoNamespace ())

    -- Gets the type of the result of the function (the type after the last "->").
    getResultType :: Type -> Type
    getResultType typ = case (unEl typ) of
      (Pi _ absType) -> getResultType $ unAbs absType
      _              -> typ

isWhereFunction :: QName -> C Bool
isWhereFunction f = do
  whereMods <- asks whereModules
  return $ any (qnameModule f `isLeChildModuleOf`) whereMods

hsTopLevelModuleName :: TopLevelModuleName -> Hs.ModuleName ()
hsTopLevelModuleName = hsModuleName . intercalate "." . map unpack
                     . List1.toList . moduleNameParts

-- | Given a module name (assumed to be a toplevel module),
-- compute the associated Haskell module name.
compileModuleName :: ModuleName -> C (HsModuleKind, Hs.ModuleName ())
compileModuleName m = do
  tlm <- liftTCM $ hsTopLevelModuleName <$> getTopLevelModuleForModuleName m
  reportSDoc "agda2hs.name" 25 $
    text "Top-level module name for" <+> prettyTCM m <+>
    text "is" <+> text (pp tlm)
  case hsModuleKind tlm of
    PrimModule -> return (PrimModule, Hs.ModuleName () "Prelude")
    HsModule   -> return (HsModule, dropHaskellPrefix tlm)
    AgdaModule -> return (AgdaModule, tlm)

importInstance :: QName -> C ()
importInstance f = do
  (kind, mod) <- compileModuleName $ qnameModule f
  unless (kind == PrimModule) $ do
    reportSLn "agda2hs.import" 20 $ "Importing instances from " ++ pp mod
    tellImport $ ImportInstances mod
