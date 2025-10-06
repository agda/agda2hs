module Agda2Hs.Compile.Postulate where

import Agda.Compiler.Backend

import Agda.Syntax.Internal
import Agda.Syntax.Common.Pretty ( prettyShow )

import Agda2Hs.Compile.Type ( compileType )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils

import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils ( hsName, pp, hsError )

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
