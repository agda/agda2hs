{-# LANGUAGE TypeApplications, NamedFieldPuns #-}

-- | Compilation to Haskell types.
module Agda2Hs.Compile.Type where

import Control.Arrow ( (>>>) )
import Control.Monad ( forM, when )
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
import Agda.TypeChecking.Reduce ( reduce, unfoldDefinitionStep )
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Utils.List ( downFrom )
import Agda.Utils.Maybe ( ifJustM, fromMaybe )
import Agda.Utils.Monad ( ifM, unlessM )
import Agda.Utils.Size ( Sized(size) )
import Agda.Utils.Functor ( ($>) )

import Agda2Hs.Compile.Name ( compileQName )
import Agda2Hs.Compile.Term ( compileVar )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.AgdaUtils
import Agda2Hs.HsUtils


-- | Type definitions from the prelude that get special translation rules.
isSpecialType :: QName -> Maybe (Elims -> C (Hs.Type ()))
isSpecialType x = case prettyShow x of
  "Haskell.Prim.Tuple._×_"    -> Just tupleType
  "Haskell.Prim.Tuple._×_×_"  -> Just tupleType
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


{- | Compile a top-level type, such that:
  
   * erased parameters of the current module are dropped.
   * usable hidden type parameters of the current module are explicitely quantified.
   * usable instance parameters are added as type constraints.
   * usable explicit parameters are forbidden (for now).
  
   The continuation is called in an extended context with these type
   arguments bound.
-}
compileTopLevelType
    :: Bool
    -- ^ Whether the generated Haskell type will end up in
    --   the final output. If so, this functions asks for
    --   language extension ScopedTypeVariables to be enabled.
    -> Type
    -> (Hs.Type () -> C a) -- ^ Continuation with the compiled type.
    -> C a
compileTopLevelType keepType t cont = do
    reportSDoc "agda2hs.compile.type" 12 $ text "Compiling top-level type" <+> prettyTCM t
    -- NOTE(flupe): even though we only quantify variable for definitions inside anonymous modules,
    --              they will still get quantified over the toplevel module parameters.
    weAreOnTop <- isJust <$> liftTCM  (currentModule >>= isTopLevelModule)
    modTel <- moduleParametersToDrop =<< currentModule
    reportSDoc "agda2hs.compile.type" 19 $ text "Module parameters to process: " <+> prettyTCM modTel
    go weAreOnTop modTel cont
  where
    go :: Bool -> Telescope -> (Hs.Type () -> C a) -> C a
    go _ EmptyTel cont = do
      ctxArgs <- getContextArgs
      ty <- compileType . unEl =<< t `piApplyM` ctxArgs
      cont ty
    go onTop (ExtendTel a atel) cont
      | not (usableModality a) =
          underAbstraction a atel $ \tel -> go onTop tel cont
      | isInstance a = do
          c <- Hs.TypeA () <$> compileType (unEl $ unDom a)
          underAbstraction a atel $ \tel ->
            go onTop tel (cont . constrainType c)
      | otherwise = do
          compileType (unEl $ unDom a)
          when (keepType && not onTop) $ tellExtension Hs.ScopedTypeVariables
          let qualifier = if onTop then id else qualifyType (absName atel)
          underAbstraction a atel $ \tel ->
            go onTop tel (cont . qualifier)


-- | Compile an Agda term into a Haskell type, along with its strictness.
compileTypeStrictness :: Term -> C (Strictness, Hs.Type ())
compileTypeStrictness t = do
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

  case t of
    Pi a b -> compileDom (absName b) a >>= \case
      DomType _ hsA -> do
        hsB <- underAbstraction a b $ compileType . unEl
        return $ Hs.TyFun () hsA hsB
      DomConstraint hsA -> do
        hsB <- underAbstraction a b (compileType . unEl)
        return $ constrainType hsA hsB
      DomDropped -> underAbstr a b (compileType . unEl)

    Def f es -> maybeUnfoldCopy f es compileType $ \f es -> do
      def <- getConstInfo f
      if | not (usableModality def) ->
            genericDocError
              =<< text "Cannot use erased definition" <+> prettyTCM f
              <+> text "in Haskell type"
         | Just semantics <- isSpecialType f -> setCurrentRange f $ semantics es
         | Just args <- allApplyElims es ->
             ifJustM (isUnboxRecord f) (\_ -> compileUnboxType f args) $
             ifM (isTransparentFunction f) (compileTransparentType args) $
             ifM (isInlinedFunction f) (compileInlineType f es) $ do
               vs <- compileTypeArgs args
               f <- compileQName f
               return $ tApp (Hs.TyCon () f) vs
         | otherwise -> fail

    Var x es | Just args <- allApplyElims es -> do
      vs <- compileTypeArgs args
      x  <- hsName <$> compileVar x
      return $ tApp (Hs.TyVar () x) vs

    Sort s -> return (Hs.TyStar ())

    Lam argInfo restAbs
      | not (keepArg argInfo) -> underAbstraction_ restAbs compileType

    _ -> fail
  where fail = genericDocError =<< text "Bad Haskell type:" <?> prettyTCM t


compileTypeArgs :: Args -> C [Hs.Type ()]
compileTypeArgs args = mapM (compileType . unArg) $ filter keepArg args


compileUnboxType :: QName -> Args -> C (Hs.Type ())
compileUnboxType r pars = do
  def <- theDef <$> getConstInfo r
  let tel = telToList $ recTel def `apply` pars
  case find keepArg tel of
    Just t  -> compileType $ unEl $ snd (unDom t)
    Nothing -> __IMPOSSIBLE__


compileTransparentType :: Args -> C (Hs.Type ())
compileTransparentType args = compileTypeArgs args >>= \case
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

compileDom :: ArgName -> Dom Type -> C CompiledDom
compileDom x a
  | usableModality a = case getHiding a of
      Instance{} -> DomConstraint . Hs.TypeA () <$> compileType (unEl $ unDom a)
      NotHidden  -> uncurry DomType <$> compileTypeStrictness (unEl $ unDom a)
      Hidden     ->
        ifM (canErase $ unDom a)
            (return DomDropped)
            (genericDocError =<< do text "Implicit type argument not supported: " <+> prettyTCM x)
  | otherwise    = return DomDropped


compileTeleBinds :: Telescope -> C [Hs.TyVarBind ()]
compileTeleBinds tel =
  forM
    (mapMaybe
      (fmap unArgDom . checkArgDom)
      (teleArgNames tel `zip` flattenTel @Type tel))
    (uncurry compileKeptTeleBind)
  where
    checkArgDom (argName, argDom) | keepArg argName = Just (argName, argDom)
    checkArgDom _ = Nothing

    unArgDom (argName, argDom) = (hsName . unArg $ argName, unDom argDom)

compileKeptTeleBind :: Hs.Name () -> Type -> C (Hs.TyVarBind ())
compileKeptTeleBind x t = do
  checkValidTyVarName x
  case compileKind t of
    Just k              -> pure $ Hs.UnkindedVar () x -- In the future we may want to show kind annotations
    _                   -> genericDocError =<<
      text "Kind of bound argument not supported:"
      <+> parens (text (Hs.prettyPrint x) <> text " : " <> prettyTCM t)

compileKind :: Type -> Maybe (Hs.Kind ())
compileKind t = case unEl t of
  Sort (Type _) -> pure (Hs.TyStar ())
  Pi a b
    | keepArg a    -> Hs.TyFun () <$> compileKind (unDom a) <*> compileKind (unAbs b)
    | otherwise    -> compileKind (unAbs b)
  _ -> Nothing     -- ^ if the argument is erased, we only compile the rest
