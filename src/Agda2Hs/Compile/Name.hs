module Agda2Hs.Compile.Name where

import Control.Arrow ( (>>>) )
import Control.Applicative ( (<|>) )
import Control.Monad
import Control.Monad.Reader

import Data.List ( intercalate, isPrefixOf )
import Data.Text ( unpack )

import qualified Language.Haskell.Exts as Hs

import Agda.Compiler.Backend hiding ( topLevelModuleName )
import Agda.Compiler.Common ( topLevelModuleName )

import Agda.Syntax.Common
import Agda.Syntax.Position
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Scope.Base ( inverseScopeLookupName )
import Agda.Syntax.TopLevelModuleName

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records ( isRecordConstructor )

import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe ( isJust, whenJust, fromMaybe, caseMaybeM )
import Agda.Utils.Pretty ( prettyShow )
import qualified Agda.Utils.Pretty as P ( Pretty(pretty) )

import Agda2Hs.AgdaUtils
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

isSpecialName :: QName -> Maybe (Hs.Name (), Maybe Import)
isSpecialName = prettyShow >>> \case
    "Agda.Builtin.Nat.Nat"         -> withImport "Numeric.Natural" "Natural"
    "Agda.Builtin.Int.Int"         -> noImport "Integer"
    "Agda.Builtin.Word.Word64"     -> noImport "Word"
    "Agda.Builtin.Float.Float"     -> noImport "Double"
    "Agda.Builtin.Bool.Bool.false" -> noImport "False"
    "Agda.Builtin.Bool.Bool.true"  -> noImport "True"
    "Haskell.Prim._∘_"             -> noImport "_._"
    "Haskell.Prim.seq"             -> noImport "seq"
    "Haskell.Prim._$!_"            -> noImport "_$!_"
    "Haskell.Prim.Monad.Dont._>>=_" -> noImport "_>>=_"
    "Haskell.Prim.Monad.Dont._>>_"  -> noImport "_>>_"
    _ -> Nothing
  where
    noImport x = Just (hsName x, Nothing)
    withImport mod x =
      let imp = Import (hsModuleName mod) Unqualified Nothing (hsName x)
      in Just (hsName x, Just imp)

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
    let (hf, mimpBuiltin) = fromMaybe (hf0, Nothing) (isSpecialName f)
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
    let (mod', mimp) = mkImport mod qual par hf
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
      (inverseScopeLookupName f <$> getScope) >>= return . \case
        (C.Qual as C.QName{} : _)
          | qual <- hsModuleName $ prettyShow as, qual /= mod
          -> QualifiedAs (Just qual)
        (C.Qual{} : _) -> QualifiedAs Nothing
        _ -> Unqualified

    qualify :: Hs.ModuleName () -> Hs.Name () -> Qualifier -> Hs.QName ()
    qualify mod n = \case
      (QualifiedAs as) -> Hs.Qual () (fromMaybe mod as) n
      Unqualified      -> Hs.UnQual () n

    primModules = ["Agda.Builtin", "Haskell.Prim", "Haskell.Prelude"]
    primMonadModules = ["Haskell.Prim.Monad.Dont", "Haskell.Prim.Monad.Do"]

    mkImport mod qual par hf
      -- make sure the Prelude is properly qualified
      | any (`isPrefixOf` pp mod) primModules
      = if isQualified qual then
          let mod' = hsModuleName "Prelude"
          in (mod', Just (Import mod' qual Nothing hf))
        else (mod, Nothing)
      | otherwise
      = (mod, Just (Import mod qual par hf))

hsTopLevelModuleName :: TopLevelModuleName -> Hs.ModuleName ()
hsTopLevelModuleName = hsModuleName . intercalate "." . map unpack
                     . List1.toList . moduleNameParts

compileModuleName :: ModuleName -> C (Hs.ModuleName ())
compileModuleName m =
  caseMaybeM
    (liftTCM $ fmap hsTopLevelModuleName <$> getTopLevelModuleForModuleName m)
    (genericDocError =<< text "Cannot compile non-existing module: " <+> prettyTCM m)
    $ \tlm -> do
      reportSDoc "agda2hs.name" 25 $
        text "Top-level module name for" <+> prettyTCM m <+>
        text "is" <+> text (pp tlm)
      return tlm
