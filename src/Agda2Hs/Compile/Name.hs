module Agda2Hs.Compile.Name where

import Control.Arrow ( (>>>) )
import Control.Monad
import Control.Monad.Reader

import Data.List ( intercalate, isPrefixOf )
import qualified Data.Map as Map
import qualified Data.Text as Text

import qualified Language.Haskell.Exts as Hs

import Agda.Compiler.Backend hiding ( topLevelModuleName )
import Agda.Compiler.Common ( topLevelModuleName )

import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Scope.Base ( Scope, scopeModules, scopeDatatypeModule, inverseScopeLookupName )
import Agda.Syntax.Scope.Monad ( isDatatypeModule )
import Agda.Syntax.TopLevelModuleName
import Agda.Syntax.Translation.AbstractToConcrete ( abstractToConcrete_ )

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records ( isRecordConstructor )

import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe ( isJust, whenJust, fromMaybe )
import Agda.Utils.Pretty ( prettyShow )
import qualified Agda.Utils.Pretty as P ( Pretty(pretty) )

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

isSpecialName :: QName -> Maybe (Hs.QName (), Maybe Import)
isSpecialName = prettyShow >>> \ case
    "Agda.Builtin.Nat.Nat"         -> withImport "Numeric.Natural" $ unqual "Natural"
    "Agda.Builtin.Int.Int"         -> noImport $ unqual "Integer"
    "Agda.Builtin.Word.Word64"     -> noImport $ unqual "Word"
    "Agda.Builtin.Float.Float"     -> noImport $ unqual "Double"
    "Agda.Builtin.Bool.Bool.false" -> noImport $ unqual "False"
    "Agda.Builtin.Bool.Bool.true"  -> noImport $ unqual "True"
    "Agda.Builtin.List.List"       -> noImport $ special Hs.ListCon
    "Agda.Builtin.List.List._∷_"   -> noImport $ special Hs.Cons
    "Agda.Builtin.List.List.[]"    -> noImport $ special Hs.ListCon
    "Agda.Builtin.Unit.⊤"          -> noImport $ special Hs.UnitCon
    "Agda.Builtin.Unit.tt"         -> noImport $ special Hs.UnitCon
    "Haskell.Prim._∘_"             -> noImport $ unqual "_._"
    "Haskell.Prim.seq"             -> noImport $ unqual "seq"
    "Haskell.Prim._$!_"            -> noImport $ unqual "_$!_"
    "Haskell.Prim.Monad.Dont._>>=_" -> noImport $ unqual "_>>=_"
    "Haskell.Prim.Monad.Dont._>>_"  -> noImport $ unqual "_>>_"
    _ -> Nothing
  where
    noImport x = Just (x, Nothing)
    withImport mod x = Just (x, Just (Import (Hs.ModuleName () mod) IsUnqualified Nothing (unQual x)))
    unqual n  = Hs.UnQual () $ hsName n
    special c = Hs.Special () $ c ()

compileName :: Applicative m => Name -> m (Hs.Name ())
compileName n = hsName . show <$> pretty (nameConcrete n)

compileQName :: QName -> C (Hs.QName ())
compileQName f
  | Just (x, mimp) <- isSpecialName f = do
      whenJust mimp tellImport
      return x
  | otherwise = do
    reportSDoc "agda2hs.name" 25 $ text $ "compiling name: " ++ prettyShow f
    f      <- isRecordConstructor f >>= \ case
      Just (r, Record{ recNamedCon = False }) -> return r -- Use the record name if no named constructor
      _                                       -> return f
    hf     <- compileName (qnameName f)
    reportSDoc "agda2hs.name" 25 $ text $ "haskell name: " ++ Hs.prettyPrint hf
    parent <- parentName f
    reportSDoc "agda2hs.name" 25 $ text $ "parent name: " ++ maybe "(none)" prettyShow parent
    mod    <- compileModuleName $ qnameModule $ fromMaybe f parent
    reportSDoc "agda2hs.name" 25 $ text $ "module name: " ++ Hs.prettyPrint mod
    currMod <- hsTopLevelModuleName <$> asks currModule
    qual   <- if | mod == currMod -> return IsUnqualified
                 | otherwise      -> isQualified (fromMaybe f parent) mod
    reportSDoc "agda2hs.name" 25 $ text $ "qualified? " ++ show qual
    par    <- traverse (compileName . qnameName) parent
    unless (skipImport mod) $ tellImport (Import mod qual par hf)
    return $ qualify mod hf qual

  where
    skipImport mod =
      "Agda.Builtin" `isPrefixOf` Hs.prettyPrint mod ||
      "Haskell.Prim" `isPrefixOf` Hs.prettyPrint mod ||
      "Haskell.Prelude" `isPrefixOf` Hs.prettyPrint mod

    parentName :: QName -> C (Maybe QName)
    parentName q = (theDef <$> getConstInfo q) >>= \case
      Constructor { conData = dt } -> return $ Just dt
      Function { funProjection = Right (Projection { projProper = Just{} , projFromType = rt }) }
        -> return $ Just $ unArg rt
      _ -> return Nothing

    isQualified :: QName -> Hs.ModuleName () -> C IsQualified
    isQualified f mod = (inverseScopeLookupName f <$> getScope) >>= \case
        (C.Qual as C.QName{} : _)
          | hsModuleName (prettyShow as) /= mod -> 
            return $ IsQualifiedAs $ hsModuleName $ prettyShow as
        (C.Qual{} : _) -> return IsQualified
        _              -> return IsUnqualified

    qualify :: Hs.ModuleName () -> Hs.Name () -> IsQualified -> Hs.QName ()
    qualify mod n IsQualified        = Hs.Qual () mod n
    qualify _   n (IsQualifiedAs as) = Hs.Qual () as n
    qualify _   n IsUnqualified      = Hs.UnQual () n

hsTopLevelModuleName :: TopLevelModuleName -> Hs.ModuleName ()
hsTopLevelModuleName = hsModuleName . intercalate "." . map Text.unpack . List1.toList . moduleNameParts

compileModuleName :: ModuleName -> C (Hs.ModuleName ())
compileModuleName m = do
  tlmn <- liftTCM $ hsTopLevelModuleName <$> getTopLevelModuleForModuleName m
  reportSDoc "agda2hs.compileModuleName" 20 $ 
    text "Top-level module name for" <+> prettyTCM m <+> 
    text "is" <+> text (show tlmn)
  return tlmn
