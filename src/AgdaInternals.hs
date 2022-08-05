-- TODO: merge upstream, useful for other backends
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
module AgdaInternals where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.Utils.Size

instance Subst Clause where
  type SubstArg Clause = DeBruijnPattern
  applySubst rhoP c@Clause{..} = c
      { clauseTel       = applyPatSubst rhoP clauseTel
      , namedClausePats = applySubst rhoP' namedClausePats
      , clauseBody      = applyPatSubst rhoP' clauseBody
      , clauseType      = applyPatSubst rhoP' clauseType
      } where rhoP' = liftS (size clauseTel) rhoP

instance Subst Defn where
  type SubstArg Defn = DeBruijnPattern
  applySubst rhoP = \case
    f@Function{..} ->
       f { funClauses  = applySubst rhoP <$> funClauses
         , funCovering = applySubst rhoP <$> funCovering }
    (PrimitiveSort q s) -> PrimitiveSort q (applyPatSubst rhoP s)
    d -> d

instance Subst Definition where
  type SubstArg Definition = DeBruijnPattern
  applySubst rhoP d@Defn{..} =
    d {defType = applyPatSubst rhoP defType, theDef = applySubst rhoP theDef}
