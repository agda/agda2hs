module Agda2Hs.Compile.Name where

import Control.Arrow ( (>>>) )
import Control.Monad
import Control.Monad.Writer ( tell )

import Data.List ( intercalate, isPrefixOf )

import qualified Language.Haskell.Exts as Hs

import Agda.Compiler.Backend hiding ( topLevelModuleName )
import Agda.Compiler.Common ( topLevelModuleName )

import Agda.Syntax.Common

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records ( isRecordConstructor )

import Agda.Utils.Maybe ( whenJust, fromMaybe )
import Agda.Utils.Pretty ( prettyShow )
import qualified Agda.Utils.Pretty as P ( Pretty(pretty) )

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
    _ -> Nothing
  where
    noImport x = Just (x, Nothing)
    withImport mod x = Just (x, Just (Import (Hs.ModuleName () mod) Nothing (unQual x)))
    unqual n  = Hs.UnQual () $ hsName n
    special c = Hs.Special () $ c ()

compileName :: Applicative m => Name -> m (Hs.Name ())
compileName n = hsName . show <$> pretty (nameConcrete n)

compileQName :: QName -> C (Hs.QName ())
compileQName f
  | Just (x, mimp) <- isSpecialName f = do
      whenJust mimp $ \imp -> tell [imp]
      return x
  | otherwise = do
    reportSDoc "agda2hs.name" 25 $ text $ "compiling name: " ++ prettyShow f
    parent <- parentName f
    f <- isRecordConstructor f >>= \ case
      Just (r, Record{ recNamedCon = False }) -> return r -- Use the record name if no named constructor
      _                                       -> return f
    hf  <- compileName (qnameName f)
    mod <- compileModuleName $ qnameModule $ fromMaybe f parent
    par <- traverse (compileName . qnameName) parent
    unless (skipImport mod) $ tell [Import mod par hf]
    -- TODO: this prints all names UNQUALIFIED. For names from
    -- qualified imports, we need to add the proper qualification in
    -- the Haskell code.
    return $ Hs.UnQual () hf

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

compileModuleName :: Monad m => ModuleName -> m (Hs.ModuleName ())
compileModuleName m = do
  ns <- traverse (pretty . nameConcrete) (mnameToList m)
  return $ Hs.ModuleName () $ intercalate "." $ map show ns
