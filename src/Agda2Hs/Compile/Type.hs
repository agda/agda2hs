{-# LANGUAGE TypeApplications #-}

-- | Compilation to Haskell types.
module Agda2Hs.Compile.Type where

import Control.Arrow ( (>>>) )
import Control.Monad ( forM, when, unless )
import Control.Monad.Trans ( lift )
import Control.Monad.Reader ( asks )
import Data.List ( find )
import Data.Maybe ( mapMaybe, isJust )
import qualified Data.Set as Set ( singleton )

import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Extension as Hs
import qualified Language.Haskell.Exts.Pretty as Hs

import Agda.Compiler.Backend hiding ( Args )

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Common.Pretty ( prettyShow )

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce ( reduce, unfoldDefinitionStep, instantiate )
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.List ( downFrom )
import Agda.Utils.Maybe ( ifJustM, fromMaybe )
import Agda.Utils.Monad ( ifM, whenM, unlessM, and2M, or2M )
import Agda.Utils.Size ( Sized(size) )
import Agda.Utils.Functor ( ($>) )

import Agda2Hs.Compile.Name ( compileQName )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.Compile.Var
import Agda2Hs.AgdaUtils
import Agda2Hs.HsUtils


-- | Type definitions from the prelude that get special translation rules.
isSpecialType :: QName -> Maybe (Elims -> C (Hs.Type ()))
isSpecialType = prettyShow >>> \case
  "Haskell.Prim.Tuple._×_"    -> Just tupleType
  "Haskell.Prim.Tuple._×_×_"  -> Just tupleType
  "Haskell.Extra.Sigma.Σ"     -> Just tupleType
  "Haskell.Extra.Erase.Erase" -> Just unitType
  "Haskell.Extra.Delay.Delay" -> Just delayType
  _                           -> Nothing


-- | Compile all the elims into a n-uple.
tupleType :: Elims -> C (Hs.Type ())
tupleType es = do
  let Just as = allApplyElims es
  ts <- mapM (compileType . unArg) as
  return $ Hs.TyTuple () Hs.Boxed ts


-- | Ignore arguments and return the unit type.
unitType :: Elims -> C (Hs.Type ())
unitType _ = return $ Hs.TyTuple () Hs.Boxed []


-- | Compile fully applied Delay type as its only type argument.
delayType :: Elims -> C (Hs.Type ())
delayType (Apply a : _) = compileType (unArg a)
delayType (_       : _) = __IMPOSSIBLE__
delayType [] = genericDocError =<< text "Cannot compile unapplied Delay type"


-- | Compile an Agda term into a Haskell type, along with its strictness.
compileTypeWithStrictness :: Term -> C (Strictness, Hs.Type ())
compileTypeWithStrictness t = do
  s <- case t of
    Def f es -> fromMaybe Lazy <$> isUnboxRecord f
    _        -> return Lazy
  ty <- compileType t
  pure (s, ty)


-- | Compile an Agda term into a Haskell type.
compileType :: Term -> C (Hs.Type ())
compileType t = do

  reportSDoc "agda2hs.compile.type" 12 $ text "Compiling type" <+> prettyTCM t
  reportSDoc "agda2hs.compile.type" 22 $ text "Compiling type" <+> pretty t

  whenM (isErasedBaseType t) fail

  instantiate t >>= \case
    Pi a b -> do
      let compileB = underAbstraction a b (compileType . unEl)
      compileDomType (absName b) a >>= \case
        DomType _ hsA -> Hs.TyFun () hsA <$> compileB
        DomConstraint hsA -> constrainType hsA <$> compileB
        DomDropped -> compileB
        DomForall hsA -> qualifyType hsA <$> compileB

    Def f es -> maybeUnfoldCopy f es compileType $ \f es -> do
      def <- getConstInfo f
      if | not (usableModality def) ->
            genericDocError
              =<< text "Cannot use erased definition" <+> prettyTCM f
              <+> text "in Haskell type"
         | Just semantics <- isSpecialType f -> setCurrentRange f $ semantics es
         | Just args <- allApplyElims es ->
             ifJustM (isUnboxRecord f) (\_ -> compileUnboxType f args) $
             ifJustM (isTupleRecord f) (\b -> compileTupleType f b args) $
             ifM (isTransparentFunction f) (compileTransparentType (defType def) args) $
             ifM (isInlinedFunction f) (compileInlineType f es) $ do
               vs <- compileTypeArgs (defType def) args
               f <- compileQName f
               return $ tApp (Hs.TyCon () f) vs
         | otherwise -> fail

    Var x es | Just args <- allApplyElims es -> do
      xi <- lookupBV x
      unless (usableModality xi) $ genericDocError
        =<< text "Cannot use erased variable" <+> prettyTCM (var x)
        <+> text "in Haskell type"
      vs <- compileTypeArgs (snd $ unDom xi) args
      x  <- hsName <$> compileDBVar x
      return $ tApp (Hs.TyVar () x) vs

    Sort s -> return (Hs.TyStar ())

    Lam argInfo restAbs -> do
      (body , x0) <- underAbstraction_ restAbs $ \b ->
        (,) <$> compileType b <*> (hsName <$> compileDBVar 0)

      -- TODO: we should also drop lambdas that can be erased based on their type
      -- (e.g. argument is of type Level/Size or in a Prop) but currently we do
      -- not have access to the type of the lambda here.
      if | hasQuantity0 argInfo -> return body
         -- Rewrite `\x -> (a -> x)` to `(->) a`
         | Hs.TyFun _ a (Hs.TyVar _ y) <- body
         , y == x0 -> return $ Hs.TyApp () (Hs.TyCon () $ Hs.Special () $ Hs.FunCon ()) a
         -- Rewrite `\x -> ((->) x)` to `(->)`
         | Hs.TyApp _ (Hs.TyCon _ (Hs.Special _ (Hs.FunCon _))) (Hs.TyVar _ y) <- body
         , y == x0 -> return $ Hs.TyCon () $ Hs.Special () $ Hs.FunCon ()
         | otherwise -> genericDocError =<< text "Not supported: type-level lambda" <+> prettyTCM t

    _ -> fail
  where fail = genericDocError =<< text "Bad Haskell type:" <?> prettyTCM t


compileTypeArgs :: Type -> Args -> C [Hs.Type ()]
compileTypeArgs ty [] = pure []
compileTypeArgs ty (x:xs) = do
  (a, b) <- mustBePi ty
  reportSDoc "agda2hs.compile.type" 16 $ text "compileTypeArgs x =" <+> prettyTCM x
  reportSDoc "agda2hs.compile.type" 16 $ text "                a =" <+> prettyTCM a
  reportSDoc "agda2hs.compile.type" 16 $ text "         modality =" <+> prettyTCM (getModality a)
  let rest = compileTypeArgs (absApp b $ unArg x) xs
  let fail msg = genericDocError =<< (text msg <> text ":") <+> parens (prettyTCM (absName b) <+> text ":" <+> prettyTCM (unDom a))
  compileDom a >>= \case
    DODropped -> rest
    DOInstance -> fail "Type-level instance argument not supported"
    DOType -> do
      (:) <$> compileType (unArg x) <*> rest
    DOTerm -> fail "Type-level term argument not supported"

compileTel :: Telescope -> C [Hs.Type ()]
compileTel EmptyTel = return []
compileTel (ExtendTel a tel) = compileDom a >>= \case
  DODropped  -> underAbstraction a tel compileTel
  DOInstance -> __IMPOSSIBLE__
  DOType     -> __IMPOSSIBLE__
  DOTerm     -> (:) <$> compileType (unEl $ unDom a) <*> underAbstraction a tel compileTel

-- Version of @compileTel@ that just computes the size,
-- and avoids compiling the types themselves.
compileTelSize :: Telescope -> C Int
compileTelSize EmptyTel = return 0
compileTelSize (ExtendTel a tel) = compileDom a >>= \case
  DODropped -> underAbstraction a tel compileTelSize
  DOInstance -> __IMPOSSIBLE__
  DOType -> __IMPOSSIBLE__
  DOTerm -> (1+) <$> underAbstraction a tel compileTelSize

compileUnboxType :: QName -> Args -> C (Hs.Type ())
compileUnboxType r pars = do
  def <- getConstInfo r
  let tel = recTel (theDef def) `apply` pars
  compileTel tel >>= \case
    [t] -> return t
    _   -> __IMPOSSIBLE__

compileTupleType :: QName -> Hs.Boxed -> Args -> C (Hs.Type ())
compileTupleType r b pars = do
  tellUnboxedTuples b
  def <- getConstInfo r
  let tel = recTel (theDef def) `apply` pars
  ts <- compileTel tel
  return $ Hs.TyTuple () b ts

compileTransparentType :: Type -> Args -> C (Hs.Type ())
compileTransparentType ty args = compileTypeArgs ty args >>= \case
  (v:vs) -> return $ v `tApp` vs
  []     -> __IMPOSSIBLE__


compileInlineType :: QName -> Elims -> C (Hs.Type ())
compileInlineType f args = do
  Function { funClauses = cs } <- theDef <$> getConstInfo f

  let [ Clause { namedClausePats = pats } ] = filter (isJust . clauseBody) cs

  when (length args < length pats) $ genericDocError =<<
    text "Cannot compile inlinable type alias" <+> prettyTCM f <+> text "as it must be fully applied."

  r <- liftReduce $ locallyReduceDefs (OnlyReduceDefs $ Set.singleton f)
                  $ unfoldDefinitionStep (Def f args) f args

  case r of
    YesReduction _ t -> compileType t
    _                -> genericDocError =<< text "Could not reduce inline type alias " <+> prettyTCM f


data DomOutput = DOInstance | DODropped | DOType | DOTerm

compileDom :: Dom Type -> C DomOutput
compileDom a = do
  isErasable <- pure (not $ usableModality a) `or2M` canErase (unDom a)
  isClassConstraint <- pure (isInstance a) `and2M` isClassType (unDom a)
  isType <- endsInSort (unDom a)
  return $ if
    | isErasable        -> DODropped
    | isClassConstraint -> DOInstance
    | isType            -> DOType
    | otherwise         -> DOTerm

-- | Compile a function type domain.
-- A domain can either be:
--
-- - dropped if the argument is erased.
-- - added as a class constraint.
-- - added as a type parameter
-- - kept as a regular explicit argument.
compileDomType :: ArgName -> Dom Type -> C CompiledDom
compileDomType x a =
  compileDom a >>= \case
    DODropped  -> pure DomDropped
    DOInstance -> DomConstraint . Hs.TypeA () <$> compileType (unEl $ unDom a)
    DOType     -> do
      -- We compile (non-erased) type parameters to an explicit forall if they
      -- come from a module parameter.
      ctx <- getContextSize
      npars <- size <$> (lookupSection =<< currentModule)
      if ctx < npars
        then do
          tellExtension Hs.ScopedTypeVariables
          return $ DomForall $ Hs.UnkindedVar () $ Hs.Ident () x
        else return $ DomDropped
    DOTerm     -> uncurry DomType <$> compileTypeWithStrictness (unEl $ unDom a)

compileTeleBinds :: Telescope -> C [Hs.TyVarBind ()]
compileTeleBinds EmptyTel = return []
compileTeleBinds (ExtendTel a tel) = do
  reportSDoc "agda2hs.compile.type" 15 $ text "Compiling type parameter: " <+> prettyTCM a
  let fail msg = genericDocError =<< (text msg <> text ":") <+> parens (prettyTCM (absName tel) <+> text ":" <+> prettyTCM (unDom a))
  compileDom a >>= \case
    DODropped  -> underAbstraction a tel compileTeleBinds
    DOType -> do
      ha <- compileKeptTeleBind (hsName $ absName tel) (unDom a)
      (ha:) <$> underAbstraction a tel compileTeleBinds
    DOInstance -> fail "Constraint in type parameter not supported"
    DOTerm -> fail "Term variable in type parameter not supported"

compileKeptTeleBind :: Hs.Name () -> Type -> C (Hs.TyVarBind ())
compileKeptTeleBind x t = do
  checkValidTyVarName x
  k <- compileKind t
  pure $ Hs.UnkindedVar () x -- In the future we may want to show kind annotations

compileKind :: Type -> C (Hs.Kind ())
compileKind t = case unEl t of
  Sort (Type _) -> pure (Hs.TyStar ())
  Pi a b -> compileDom a >>= \case
    DODropped -> underAbstraction a b compileKind
    DOType -> Hs.TyFun () <$> compileKind (unDom a) <*> underAbstraction a b compileKind
    DOTerm -> err
    DOInstance -> err
  _ -> err
  where
    err = genericDocError =<< text "Not a valid Haskell kind: " <+> prettyTCM t
