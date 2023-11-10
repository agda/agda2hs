module Agda2Hs.Compile.Name where

import Control.Arrow ( (>>>) )
import Control.Applicative ( (<|>) )
import Control.Monad
import Control.Monad.Except ( catchError )
import Control.Monad.Reader

import Data.Functor ( (<&>) )
import Data.List ( intercalate, isPrefixOf )
import Data.Text ( unpack )

import qualified Language.Haskell.Exts as Hs

import Agda.Compiler.Backend hiding ( topLevelModuleName )
import Agda.Compiler.Common ( topLevelModuleName )

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common
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

import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe ( isJust, isNothing, whenJust, fromMaybe, caseMaybeM )

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Rewrites
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

isSpecialCon :: QName -> Maybe (Hs.QName ())
isSpecialCon = prettyShow >>> \case
    "Agda.Builtin.List.List"     -> special Hs.ListCon
    "Agda.Builtin.List.List._∷_" -> special Hs.Cons
    "Agda.Builtin.List.List.[]"  -> special Hs.ListCon
    "Agda.Builtin.Unit.⊤"       -> special Hs.UnitCon
    "Agda.Builtin.Unit.tt"       -> special Hs.UnitCon
    _ -> Nothing
  where special c = Just (Hs.Special () $ c ())

-- Gets an extra parameter, with the user-defined rewrite rules in it.
-- If finds it in the user-defined or the built-in rewrite rules, then it returns the new name and a possible import in a Just; otherwise returns Nothing.
isSpecialName :: QName -> Rewrites -> Maybe (Hs.Name (), Maybe Import)
isSpecialName f rules = let pretty = prettyShow f in case lookupRules pretty rules of
    result@(Just _)     -> result
    Nothing             -> case pretty of
      "Agda.Builtin.Nat.Nat"          -> withImport "Numeric.Natural" "Natural"
      "Haskell.Control.Monad.guard"   -> withImport "Control.Monad" "guard"
      "Agda.Builtin.Int.Int"          -> noImport "Integer"
      "Agda.Builtin.Word.Word64"      -> noImport "Word"
      "Agda.Builtin.Float.Float"      -> noImport "Double"
      "Agda.Builtin.Bool.Bool.false"  -> noImport "False"
      "Agda.Builtin.Bool.Bool.true"   -> noImport "True"
      "Haskell.Prim._∘_"              -> noImport "_._"
      "Haskell.Prim.seq"              -> noImport "seq"
      "Haskell.Prim._$!_"             -> noImport "_$!_"
      "Haskell.Prim.Monad.Dont._>>=_" -> noImport "_>>=_"
      "Haskell.Prim.Monad.Dont._>>_"  -> noImport "_>>_"
      _                               -> Nothing
  where
    noImport x = Just (hsName x, Nothing)
    withImport mod x =
      let imp = Import (hsModuleName mod) Unqualified Nothing (hsName x) (Hs.NoNamespace ())
                                                                       -- ^ TODO: add an option to specify this in the config file (whether it is a type or not)
                                                                       -- as far as I know, there are no type operators in Prelude, but maybe a self-defined one could cause trouble
      in Just (hsName x, Just imp)

    lookupRules :: String -> Rewrites -> Maybe (Hs.Name (), Maybe Import)
    lookupRules _ [] = Nothing
    lookupRules pretty (rule:ls)
      | pretty == from rule   = case (importing rule) of     -- check if there is a new import
          Just lib -> withImport lib (to rule)
          Nothing  -> noImport (to rule)
      | otherwise             = lookupRules pretty ls

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
      Just (r, Record{recNamedCon = False}) -> r -- use record name for unnamed constructors
      _                                     -> f
    hf0 <- compileName (qnameName f)
    rules <- asks rewrites
    let (hf, mimpBuiltin) = fromMaybe (hf0, Nothing) (isSpecialName f rules)
    parent <- parentName f
    par <- traverse (compileName . qnameName) parent
    let mod0 = qnameModule $ fromMaybe f parent
    mod <- compileModuleName mod0
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
      (mod', mimp) = mkImport mod qual par hf namespace
      qf = qualify mod' hf qual

    -- add (possibly qualified) import
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

    primModules = ["Agda.Builtin", "Haskell.Prim", "Haskell.Prelude"]
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

    mkImport mod qual par hf maybeIsType
      -- make sure the Prelude is properly qualified
      | any (`isPrefixOf` pp mod) primModules
      = if isQualified qual then
          let mod' = hsModuleName "Prelude"
          in (mod', Just (Import mod' qual Nothing hf maybeIsType))
        else (mod, Nothing)
      | otherwise
      = (mod, Just (Import mod qual par hf maybeIsType))

hsTopLevelModuleName :: TopLevelModuleName -> Hs.ModuleName ()
hsTopLevelModuleName = hsModuleName . intercalate "." . map unpack
                     . List1.toList . moduleNameParts

-- | Given a module name (assumed to be a toplevel module), 
-- compute the associated Haskell module name.
compileModuleName :: ModuleName -> C (Hs.ModuleName ())
compileModuleName m = do
  tlm <- liftTCM $ hsTopLevelModuleName <$> getTopLevelModuleForModuleName m
  reportSDoc "agda2hs.name" 25 $
    text "Top-level module name for" <+> prettyTCM m <+>
    text "is" <+> text (pp tlm)
  return tlm
