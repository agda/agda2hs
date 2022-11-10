module Agda2Hs.Compile.Name where

import Control.Arrow ( (>>>) )

import qualified Language.Haskell.Exts.Syntax as Hs

import Agda.Compiler.Backend hiding ( topLevelModuleName )
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
    -- TODO: this prints all names UNQUALIFIED. For names from
    -- qualified imports, we need to add the proper qualification in
    -- the Haskell code.
    mkname :: QName -> C (Hs.QName ())
    mkname x = do
      s <- fmap show $ pretty $ nameConcrete $ qnameName x
      return $ Hs.UnQual () (hsName s)
