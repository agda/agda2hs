{-# LANGUAGE OverloadedStrings #-}

module Agda2Hs.Compile.RuntimeCheckUtils (importDec, checkNoneErased, smartConstructor, NestedLevel (Odd), alternatingLevels, recordLevels, RtcResult (..), checkRtc) where

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import qualified Agda.Syntax.Concrete as AC
import Agda.Syntax.Concrete.Definitions (NiceEnv (NiceEnv), niceDeclarations, runNice)
import qualified Agda.Syntax.Concrete.Name as AN
import Agda.Syntax.Internal
import Agda.Syntax.Position (noRange)
import Agda.Syntax.Translation.ConcreteToAbstract (ToAbstract (toAbstract))
import Agda.TypeChecking.InstanceArguments (findInstance)
import Agda.TypeChecking.MetaVars (newInstanceMeta, newLevelMeta)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty (PrettyTCM (prettyTCM), (<+>))
import Agda.TypeChecking.Reduce (instantiate)
import Agda.TypeChecking.Substitute (telView', theTel)
import Agda.TypeChecking.Telescope (splitTelescopeAt)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.List (initLast)
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Monad (allM, partitionM, unless)
import Agda2Hs.Compile.Term (compileTerm)
import Agda2Hs.Compile.Type (DomOutput (DODropped), compileDom)
import Agda2Hs.Compile.Types (C)
import Agda2Hs.Compile.Utils
import Agda2Hs.Language.Haskell.Utils
import Control.Monad.Except (catchError)
import Control.Monad.State (StateT (StateT, runStateT))
import Data.List (intersect)
import Data.Map (empty)
import Data.Maybe (catMaybes, fromJust, isJust)
import Data.Tree (flatten, unfoldTree)
import Data.Tuple (swap)
import qualified Language.Haskell.Exts as Hs

-- Import Haskell.Extra.Dec
-- based on Agda.Syntax.Translation.ConcreteToAbstract.importPrimitives
importDec :: TCM ()
importDec = do
  let haskellExtra = AN.Qual (AC.simpleName "Haskell") . AN.Qual (AC.simpleName "Extra")
      decname = AC.simpleName "Dec"
      directives = ImportDirective noRange UseEverything [] [] Nothing
      importDecl q = [AC.Import noRange (haskellExtra q) Nothing AC.DontOpen directives]
      decl = importDecl $ AC.QName decname
      nicedec = fst $ runNice (NiceEnv True AC.NoWhere_) $ niceDeclarations empty decl
  ads <- case nicedec of
    Left _ -> __IMPOSSIBLE__
    Right ds -> toAbstract ds
  return ()

-- Retrieve constructor name and generated smart constructor qname.
-- Takes extra argument whether one additional name should be stripped
smartConstructor :: QName -> Bool -> C QName
smartConstructor qname strip1 = do
  checkNameConflict smartString
  return smartQName
  where
    qnameList = qnameToList qname
    -- data types need the name of the data type itself stripped
    strip = if strip1 then 2 else 1
    qualifier = List1.take (length qnameList - strip) qnameList
    name = List1.last qnameList
    smartString = "sc" ++ prettyShow name
    smartName = mkName (nameBindingSite name) (nameId name) smartString
    smartQName = qnameFromList $ List1.prependList qualifier $ smartName List1.:| []

-- Only preconditions on odd levels of nesting should incur a check
-- because only they can be violated from Haskell
-- See Findler and Felleisen, Contracts for Higher-Order Functions, ICFP 2002
data NestedLevel = Odd | Even

-- Expected only to be used with infinite lists. Stream would be
-- more faithful, but we use lists for dependency simplicity.
whenOdd :: [NestedLevel] -> [a] -> [a]
whenOdd (Odd : _) l = l
whenOdd (Even : _) _ = []

alternatingLevels :: [NestedLevel]
alternatingLevels = cycle [Odd, Even]

-- For records, both the fields and their types should be considered to be in odd position
recordLevels :: [NestedLevel]
recordLevels = Odd : alternatingLevels

-- Runtime checks are not supported for certain pragmas.
-- Check that the telescope has no erased types.
checkNoneErased :: Telescope -> [NestedLevel] -> C Bool
checkNoneErased tel ls = do
  let doms = telToList tel
  (erased, other) <- partitionM ((`checkTopOrDataErased` ls) . fst) $
                       zip doms $ map (domToTel . (snd <$>)) doms
  (null erased &&) <$> allM ((`checkNoneErased` ls) . snd) other

-- Check if a type is erased or contains an erased type within a data type or record.
-- In this case, it should be checked.
checkTopOrDataErased :: Dom (a, Type) -> [NestedLevel] -> C Bool
checkTopOrDataErased d (_ : ls) = do
  let domType = snd <$> d
      unfold = unfoldTypes [unDom domType]
      -- do not recurse into Pi at top level (that is still handled by caller),
      -- but do at `Apply` levels below
      tels = [domToTel t | Pi t _ <- map unArg unfold]
      quantities = getQuantity d : map getQuantity unfold
  domDropped <- (DODropped ==) <$> compileDom domType
  (or (domDropped : [True | Quantity0 _ <- quantities]) ||) . not . and <$> mapM (`checkNoneErased` ls) tels

-- External runtime check result
data RtcResult
  = NoneErased
  | Uncheckable
  | Checkable [Hs.Decl ()]

-- Internal runtime check result
data RtcResult'
  = NoneErased'
  | Uncheckable'
  | -- The actual runtime check is assembled in the caller receiving an RtcResult',
    -- because the logic at the top level is different, e.g. the declarations are
    -- put in a `where` instead of being flattened.
    Checkable'
      { theirLhs :: [Hs.Pat ()],
        theirChks :: [Hs.Exp ()],
        theirRhs :: [Hs.Exp ()],
        theirDecls :: [Hs.Decl ()]
      }

-- Check name induces no conflict
checkNameConflict :: String -> C ()
checkNameConflict s =
  testResolveStringName s >>= \case
    Just _ -> errorNameConflict s
    Nothing -> return ()

errorWhenConflicts :: [String] -> C ()
errorWhenConflicts [] = pure ()
errorWhenConflicts (c : _) = errorNameConflict c

errorNameConflict :: String -> C ()
errorNameConflict s =
  genericDocError
    =<< ("Illegal name" <+> prettyTCM s) <> ", conflicts with name generated for runtime checks."

-- Create runtime check.
-- Takes function name, lhs patterns, expressions for checks, expression on success,
-- and optionally `where` binds
createRtc :: Hs.Name () -> [Hs.Pat ()] -> [Hs.Exp ()] -> Hs.Exp () -> Maybe (Hs.Binds ()) -> Hs.Decl ()
createRtc n args [] success = createRtc' n args $ Hs.UnGuardedRhs () success
createRtc n args chks success =
  createRtc' n args rhs
  where
    rhs = Hs.GuardedRhss () $ Hs.GuardedRhs () [Hs.Qualifier () andChks] success : notChks ++ [otherwiseChk]
    andChks = foldr1 (\c -> Hs.InfixApp () c $ Hs.QVarOp () $ Hs.UnQual () $ Hs.Symbol () "&&") chks
    chk2err chk =
      let msg = "Runtime check failed: " ++ Hs.prettyPrint chk
       in Hs.App () (hsVar "error") $ Hs.Lit () $ Hs.String () msg msg
    errs = zip chks $ map chk2err chks
    (nots, otherwise) = fromJust $ initLast errs
    notChks = map (\(chk, err) -> Hs.GuardedRhs () [Hs.Qualifier () $ Hs.App () (hsVar "not") chk] err) nots
    otherwiseChk = (\(_, err) -> Hs.GuardedRhs () [Hs.Qualifier () $ hsVar "otherwise"] err) otherwise

createRtc' :: Hs.Name () -> [Hs.Pat ()] -> Hs.Rhs () -> Maybe (Hs.Binds ()) -> Hs.Decl ()
createRtc' n args rhs binds = Hs.FunBind () [Hs.Match () n args rhs binds]

{- Suffixes for `go` functions in the `where` declaration for nested
erased arguments and `a` arguments for unnamed arguments.
Example to show all cases:

Turning

tripleOdd : (((m : Nat) → @0 IsTrue (m > 0) → (((n : Nat) → @0 IsFalse (n < 1) → Nat) → Nat) → Nat) → Nat) → Nat

into

tripleOdd a0 = TripleOdd.PostRtc.tripleOdd (\ a1 -> a0 (go1 a1))
  where
    go1 up m a2
      | decIsTrue (m > 0) = up m (\ a3 -> a2 (go0 a3))
      | otherwise = error "Runtime check failed: decIsTrue (m > 0)"
      where
        go0 up n
          | decIsFalse (n < 1) = up n
          | otherwise = error "Runtime check failed: decIsFalse (n < 1)"

has a tree of

(((m : Nat) → @0 … → (((n : Nat) → @0 … → Nat) → Nat) → Nat) → Nat) → Nat ~ (0, 0)
Reserve a0 for ((Nat → ((Nat → Nat) → Nat) → Nat) → Nat):
  ((m : Nat) → @0 … → (((n : Nat) → @0 … → Nat) → Nat) → Nat) → Nat ~ (0, 1)
Reserve a1 for (Nat → ((Nat → Nat) → Nat) → Nat):
    (m : Nat) → @0 … → (((n : Nat) → @0 … → Nat) → Nat) → Nat ~ (0, 2)
Reserve a2 for ((Nat → Nat) → Nat):
      ((n : Nat) → @0 … → Nat) → Nat ~ (0, 3)
Reserve a3 for (Nat → Nat):
        (n : Nat) → @0 … → Nat ~ (0, 4)
        ~ (0, 4), lhs = ["n"], chks = ["decIsFalse n < 1"], rhs = ["n"], decls = []
Reserve go0 for (((Nat → Nat) → Nat) → Nat):
      ~ (1, 4), lhs = ["a3"], chks = [], rhs = ["go0 a3"], decls = ["go0 up n = …"]
Inline:
    ~ (1, 4), lhs = ["m", "a2"], chks = ["decIsTrue (m > 0)"], rhs = ["m (\ a3 -> a2 (go0 a3))"], decls = ["go0 up n = …"]
Reserve go1 for ((Nat → ((Nat → Nat) → Nat) → Nat) → Nat → ((Nat → Nat) → Nat) → Nat):
  ~ (2, 4), lhs = ["a1"], chks = [], rhs = ["go1 a1"], decls = ["go1 up m a2 = …"]
Inline:
~ (2, 4), lhs = ["a0"], chks = [], rhs = ["(\ a1 -> a0 (go1 a1))"], decls = ["go1 up m a2 = …"]
-}
type NameIndices = (Int, Int)

-- Creates a runtime check if necessary and possible, informing C accordingly.
-- Takes telescope of type to check, name, level of nesting stream, and expression on success.
checkRtc :: Telescope -> QName -> Hs.Exp () -> [NestedLevel] -> C RtcResult
checkRtc tel name success lvls = do
  (_, chk) <- checkRtc' (0, 0) tel lvls
  case chk of
    NoneErased' -> return NoneErased
    Uncheckable' -> return Uncheckable
    Checkable' {..} -> do
      tellAllCheckable name
      let rhs = eApp success theirRhs
          chkName = hsName $ prettyShow $ qnameName name
          chk = createRtc chkName theirLhs theirChks rhs $ if null theirDecls then Nothing else Just $ Hs.BDecls () theirDecls
      return $ Checkable [chk]

-- Recursively check for runtime checkability in nested types.
-- Accumulates on name indices for `go` function and `a` argument.
-- Takes telescope of type to check.
checkRtc' :: NameIndices -> Telescope -> [NestedLevel] -> C (NameIndices, RtcResult')
checkRtc' idcs tel lvls = do
  -- Partition out arguments that are erased and at top level (those we will attempt to check)
  (erased, call) <- partitionM ((`checkTopOrDataErased` lvls) . fst) $ zip doms telsUpTo
  ourChks <- uncurry createGuardExp `mapM` whenOdd lvls erased
  -- Recursively accumulate checks on arguments below top level
  (belowIdcs, belowChks) <- mapAccumLM checkRtc'' idcs $ map (,lvls) call
  (belowIdcs,)
    <$> if not $ all isJust belowChks && all isJust ourChks
      then return Uncheckable'
      else -- all checkable or none erased
        let (theirLhs, theirRhs, decls) = unzip3 $ catMaybes belowChks
            theirDecls = concat decls
            -- all checks below found an instance
            theirChks = catMaybes ourChks
         in if null theirDecls && null erased
              then return NoneErased'
              else return Checkable' {..}
  where
    doms = telToList tel
    telsUpTo = map (\i -> fst $ splitTelescopeAt i tel) [0 ..]

-- Check a single type for runtime checkability.
-- Accumulates on name indices for `go` function and `a` argument.
-- Takes domain of type and telescope up to that point for context.
-- If checkable, returns lhs and rhs at that point plus declarations from checks below.
checkRtc'' ::
  NameIndices ->
  ((Dom (ArgName, Type), Telescope), [NestedLevel]) ->
  C (NameIndices, Maybe (Hs.Pat (), Hs.Exp (), [Hs.Decl ()]))
checkRtc'' (goIdx, argIdx) ((d, tUpTo), _ : lvls) =
  -- Mutual recursion with checkRtc'
  addContext tUpTo (checkRtc' (goIdx, ourArgIdx) tAt lvls) >>= \case
    (idcs, NoneErased') -> return (idcs, Just (ourLhs, argVar, []))
    (idcs, Uncheckable') -> return (idcs, Nothing)
    ((theirGoIdx, theirArgIdx), Checkable' {..}) -> do
      let go = "go" ++ show theirGoIdx
          conflicts = tAtNames `intersect` [go, arg, up]
      errorWhenConflicts conflicts
      let (ourGoIdx, ourRhs, ourRtc) =
            if null theirChks
              then -- inline if nothing to check at this level (consumes no `goIdx`)
              -- e.g. `\ a3 -> a2 (go0 a3)`, continuing the example above `NameIndices`
                (theirGoIdx, Hs.Lambda () theirLhs $ argVar `eApp` theirRhs, theirDecls)
              else
                let -- e.g. `up m a2`
                    lhs = hsPat up : theirLhs
                    -- e.g. `up m (\ a3 -> a2 (go0 a3))`
                    rhs = hsVar up `eApp` theirRhs
                    rtc = createRtc (hsName go) lhs theirChks rhs $ binds theirDecls
                 in -- e.g. `go1 a1`
                    (succ theirGoIdx, hsVar go `eApp` [argVar], [rtc])
      return ((ourGoIdx, theirArgIdx), Just (ourLhs, ourRhs, ourRtc))
  where
    tAt = domToTel $ snd <$> d
    tAtNames = map (fst . unDom) $ telToList tAt
    name = fst $ unDom d
    -- Use arg name if available, otherwise insert one (consumes one on `argIdx`)
    (arg, ourArgIdx) = if name == "_" then ("a" ++ show argIdx, succ argIdx) else (name, argIdx)
    ourLhs = hsPat arg
    argVar = hsVar arg
    up = "up"

---- Small convenience functions

-- Gather telescope from domain
domToTel :: Dom Type -> Telescope
domToTel = theTel . telView' . unDom

-- Unfold data types and records from list of types
unfoldTypes :: [Type] -> [Arg Term]
unfoldTypes tys =
  concat $
    flatten $
      ( \tes ->
          let argss = [[a | Apply a <- es] | Def _ es <- tes]
           in (concat argss, map (map unArg) argss)
      )
        `unfoldTree` map unEl tys

-- Create binds from declarations except when empty
binds :: [Hs.Decl ()] -> Maybe (Hs.Binds ())
binds [] = Nothing
binds decls = Just $ Hs.BDecls () decls

-- Turn a type into its Dec version
decify :: Type -> C Type
decify t = do
  dec <- resolveStringName "Haskell.Extra.Dec"
  level <- liftTCM newLevelMeta
  let vArg = defaultArg
      hArg = setHiding Hidden . vArg
  return $ t {unEl = Def dec $ map Apply [hArg $ Level level, vArg $ unEl t]}

-- Failably find instances for decidable terms
findDecInstances :: Type -> TCMT IO (Maybe Term)
findDecInstances t =
  do
    (m, v) <- newInstanceMeta "" t
    findInstance m Nothing
    Just <$> instantiate v
    `catchError` return (return Nothing)

-- Create expression to be put in the guard
createGuardExp :: Dom (a, Type) -> Telescope -> C (Maybe (Hs.Exp ()))
createGuardExp dom telUpTo = addContext telUpTo $ do
  dec <- decify $ snd $ unDom dom
  liftTCM (findDecInstances dec) >>= traverse (compileTerm dec)

-- from GHC.Utils.Monad
mapAccumLM :: (Monad m, Traversable t) => (acc -> x -> m (acc, y)) -> acc -> t x -> m (acc, t y)
mapAccumLM f s = fmap swap . flip runStateT s . traverse f'
  where
    f' = StateT . (fmap . fmap) swap . flip f
