module Agda2Hs.Compile.Name where

import Control.Arrow ( (>>>) )
import Control.Monad
import Control.Monad.Reader

import Data.List ( intercalate, isPrefixOf )
import Data.Text ( unpack )

import qualified Language.Haskell.Exts as Hs

import Agda.Compiler.Backend hiding ( topLevelModuleName )
import Agda.Compiler.Common ( topLevelModuleName )

import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Scope.Base ( inverseScopeLookupName )
import Agda.Syntax.TopLevelModuleName

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records ( isRecordConstructor )

import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe ( whenJust, fromMaybe, caseMaybeM )
import Agda.Utils.Pretty ( prettyShow )
import qualified Agda.Utils.Pretty as P ( Pretty(pretty) )

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

isSpecialName :: QName -> Maybe (Hs.QName (), Maybe Import)
isSpecialName = prettyShow >>> \case
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
    withImport mod x = Just (x, Just (Import (Hs.ModuleName () mod) Unqualified Nothing (unQual x)))
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
    f       <- isRecordConstructor f >>= return . \case
      Just (r, Record{recNamedCon = False}) -> r -- use record name for unnamed constructors
      _                                     -> f
    hf      <- compileName (qnameName f)
    parent  <- parentName f
    mod     <- compileModuleName $ qnameModule $ fromMaybe f parent
    currMod <- hsTopLevelModuleName <$> asks currModule
    qual    <- if | mod == currMod -> return Unqualified
                  | otherwise      -> getQualifier (fromMaybe f parent) mod
    reportSDoc "agda2hs.name" 25 $ text
       $ "compiling name: " ++ prettyShow f
      ++ "\nhaskell name: " ++ Hs.prettyPrint hf
      ++ "\nparent name: " ++ prettyShow parent
      ++ "\nmodule name: " ++ Hs.prettyPrint mod
      ++ "\nqualifier: " ++ prettyShow (fmap (fmap pp) qual)
    par <- traverse (compileName . qnameName) parent
    unless (skipImport mod) $ tellImport (Import mod qual par hf)
    return $ qualify mod hf qual

  where
    skipImport mod =
      "Agda.Builtin" `isPrefixOf` Hs.prettyPrint mod ||
      "Haskell.Prim" `isPrefixOf` Hs.prettyPrint mod ||
      "Haskell.Prelude" `isPrefixOf` Hs.prettyPrint mod

    parentName :: QName -> C (Maybe QName)
    parentName q = (theDef <$> getConstInfo q) >>= return . \case
      Constructor {conData = dt} -> Just dt
      Function {funProjection = proj}
        | Right (Projection {projProper = Just{}, projFromType = rt}) <- proj
        -> Just $ unArg rt
      _ -> Nothing

    getQualifier :: QName -> Hs.ModuleName () -> C Qualifier
    getQualifier f mod = (inverseScopeLookupName f <$> getScope) >>= return . \case
      (C.Qual as C.QName{} : _)
        | qual <- hsModuleName $ prettyShow as, qual /= mod
        -> QualifiedAs (Just qual)
      (C.Qual{} : _) -> QualifiedAs Nothing
      _ -> Unqualified

    qualify :: Hs.ModuleName () -> Hs.Name () -> Qualifier -> Hs.QName ()
    qualify mod n = \case
      (QualifiedAs as) -> Hs.Qual () (fromMaybe mod as) n
      Unqualified      -> Hs.UnQual () n

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
