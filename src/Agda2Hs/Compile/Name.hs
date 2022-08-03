module Agda2Hs.Compile.Name where

import Control.Arrow ( (>>>) )

import qualified Language.Haskell.Exts.Syntax as Hs

import Agda.Compiler.Backend
import Agda.Compiler.Common ( topLevelModuleName )

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records ( isRecordConstructor )

import Agda.Utils.Pretty ( prettyShow )
import qualified Agda.Utils.Pretty as P ( Pretty(pretty) )

import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

isSpecialName :: QName -> Maybe (Hs.QName ())
isSpecialName = prettyShow >>> \ case
    "Agda.Builtin.Nat.Nat"         -> unqual "Natural"
    "Agda.Builtin.Int.Int"         -> unqual "Integer"
    "Agda.Builtin.Word.Word64"     -> unqual "Word"
    "Agda.Builtin.Float.Float"     -> unqual "Double"
    "Agda.Builtin.Bool.Bool.false" -> unqual "False"
    "Agda.Builtin.Bool.Bool.true"  -> unqual "True"
    "Agda.Builtin.List.List"       -> special Hs.ListCon
    "Agda.Builtin.List.List._∷_"   -> special Hs.Cons
    "Agda.Builtin.List.List.[]"    -> special Hs.ListCon
    "Agda.Builtin.Unit.⊤"          -> special Hs.UnitCon
    "Agda.Builtin.Unit.tt"         -> special Hs.UnitCon
    "Haskell.Prim._∘_"             -> unqual "_._"
    "Haskell.Prim.seq"             -> unqual "seq"
    "Haskell.Prim._$!_"            -> unqual "_$!_"
    _ -> Nothing
  where
    unqual n  = Just $ Hs.UnQual () $ hsName n
    special c = Just $ Hs.Special () $ c ()

hsQName :: QName -> C (Hs.QName ())
hsQName f
  | Just x <- isSpecialName f = return x
  | otherwise = do
    liftTCM (isRecordConstructor f) >>= \ case
      Just (r, Record{ recNamedCon = False }) -> mkname r -- Use the record name if no named constructor
      _                                       -> mkname f
  where
    mkname x = do
      reportSDoc "agda2hs" 14 $ text "Compiling name: " <+> prettyTCM x
      m <- topLevelModuleName =<< currentModule
      reportSDoc "agda2hs" 19 $ text "Current module: " <+> prettyTCM m
      s <- showTCM x
      reportSDoc "agda2hs" 54 $ text "Raw name:   " <+> pure (P.pretty x)
      reportSDoc "agda2hs" 59 $ text "Raw module: " <+> pure (P.pretty m)
      return $
        case break (== '.') $ reverse s of
          (_, "")      -> Hs.UnQual () (hsName s)
          (fr, _ : mr)
            -- Agda 2.6.2 changed how functions in where clauses get qualified. To work around that
            -- we never qualify things from the current module.
            | x `isInModule` m -> Hs.UnQual () (hsName $ reverse fr)
            | otherwise        -> Hs.Qual () (Hs.ModuleName () $ reverse mr) (hsName $ reverse fr)
