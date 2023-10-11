module Agda2Hs.Compile.Postulate where

import qualified Language.Haskell.Exts.Syntax as Hs

import Agda.Compiler.Backend

import Agda.Syntax.Internal
import Agda.Syntax.Common.Pretty ( prettyShow )

import Agda2Hs.Compile.Type ( compileType )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

compilePostulate :: Definition -> C [Hs.Decl ()]
compilePostulate def = do
  let n = qnameName (defName def)
      x = hsName $ prettyShow n
  checkValidFunName x
  setCurrentRange (nameBindingSite n) $ do
    ty <- compileType (unEl $ defType def)
    let body = hsError $ "postulate: " ++ pp ty
    return [ Hs.TypeSig () [x] ty
           , Hs.FunBind () [Hs.Match () x [] (Hs.UnGuardedRhs () body) Nothing] ]
