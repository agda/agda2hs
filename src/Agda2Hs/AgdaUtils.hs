module Agda2Hs.AgdaUtils where

import Data.Maybe

import Agda.Compiler.Backend
import Agda.TypeChecking.Pretty
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Substitute
import Agda.Utils.Pretty ( prettyShow )
import Agda.Utils.Impossible

multilineText :: Monad m => String -> m Doc
multilineText s = vcat $ map text $ lines s

(~~) :: QName -> String -> Bool
q ~~ s = prettyShow q == s

applyNoBodies :: Definition -> [Arg Term] -> Definition
applyNoBodies d args = revert $ d `apply` args
  where
    bodies :: [Maybe Term]
    bodies = map clauseBody $ funClauses $ theDef d

    setBody cl b = cl { clauseBody = b }

    revert :: Definition -> Definition
    revert d@(Defn {theDef = f@(Function {funClauses = cls})}) =
      d {theDef = f {funClauses = zipWith setBody cls bodies}}
    revert _ = __IMPOSSIBLE__

-- | Convert the final 'Proj' projection elimination into a
--   'Def' projection application.
unSpine1 :: Term -> Term
unSpine1 v =
  case hasElims v of
    Just (h, es) -> fromMaybe v $ loop h [] es
    Nothing      -> v
  where
    loop :: (Elims -> Term) -> Elims -> Elims -> Maybe Term
    loop h res es =
      case es of
        []             -> Nothing
        Proj o f : es' -> Just $ fromMaybe (Def f (Apply (defaultArg v) : es')) $ loop h (Proj o f : res) es'
        e        : es' -> loop h (e : res) es'
      where v = h $ reverse res
