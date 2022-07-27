module Agda2Hs.Compile.Record where

import Control.Arrow ( (>>>), (***), (&&&), first, second )
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader

import Data.Generics ( mkT, everywhere, listify, extT, everything, mkQ, Data )
import Data.List
import Data.List.NonEmpty ( NonEmpty(..) )
import Data.Maybe
import Data.Map ( Map )
import qualified Data.Text as Text
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap

import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Build as Hs
import qualified Language.Haskell.Exts.Parser as Hs
import qualified Language.Haskell.Exts.Extension as Hs

import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.BasicOps

import Agda.Syntax.Common hiding ( Ranged )
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad hiding ( withCurrentModule )

import Agda.TypeChecking.CheckInternal ( infer )
import Agda.TypeChecking.Constraints ( noConstraints )
import Agda.TypeChecking.Conversion ( equalTerm )
import Agda.TypeChecking.InstanceArguments ( findInstance )
import Agda.TypeChecking.Level ( isLevelType )
import Agda.TypeChecking.MetaVars ( newInstanceMeta )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce ( instantiate, reduce )
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Records
import Agda.TypeChecking.Sort ( ifIsSort )

import Agda.Utils.Lens
import Agda.Utils.Pretty ( prettyShow )
import qualified Agda.Utils.Pretty as P
import Agda.Utils.List
import Agda.Utils.Impossible
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Functor

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.ClassInstance
import Agda2Hs.Compile.Function
import Agda2Hs.Compile.Name
import Agda2Hs.Compile.Type
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils
import Agda2Hs.Pragma

-- Primitive fields and default implementations
type MinRecord = ([Hs.Name ()], Map (Hs.Name ()) (Hs.Decl ()))

withMinRecord :: QName -> C a -> C a
withMinRecord m = local $ \ e -> e { minRecordName = Just (qnameToMName m) }

compileMinRecord :: [Hs.Name ()] -> QName -> C MinRecord
compileMinRecord fieldNames m = do
  rdef <- getConstInfo m
  definedFields <- classMemberNames rdef
  let Record{recPars = npars} = theDef rdef
      pars = map defaultArg [ Var i [] | i <- [npars, npars - 1..0] ]
  defaults <- lookupDefaultImplementations m (fieldNames \\ definedFields)
  -- We can't simply compileFun here for two reasons:
  -- * it has an explicit dictionary argument
  -- * it's using the fields and definitions from the minimal record and not the parent record
  compiled <- withMinRecord m $ fmap concat $ traverse (compileFun . (`apply` pars)) defaults
  let declMap = Map.fromList [ (definedName c, def) | def@(Hs.FunBind _ (c : _)) <- compiled ]
  return (definedFields, declMap)

compileMinRecords :: Definition -> [String] -> C [Hs.Decl ()]
compileMinRecords def sls = do

  members <- classMemberNames def

  qnames <- traverse resolveStringName sls
  (prims, defaults) <- unzip <$> traverse (compileMinRecord members) qnames

  -- 0. [OPTIONAL] check all record signatures match (or simply leave to GHC)

  -- 1. build minimal pragma

  let
    -- make the formula for a list of names of methods for for a single minimal instance
    helpAnd :: [Hs.Name ()] -> Hs.BooleanFormula ()
    helpAnd xs = Hs.AndFormula () $ Hs.VarFormula () <$> xs

    -- combine formulae for all minimal instances
    helpOr :: [Hs.BooleanFormula ()] -> Hs.Decl ()
    helpOr bs = Hs.MinimalPragma () (Just $ Hs.OrFormula () bs)

    minPragma = helpOr (map helpAnd prims)

  -- 2. assert that all default implementations are the same (for a certain field)
  let getUnique f (x :| xs)
        | all (x ==) xs = return x
        | otherwise     = genericDocError =<< do text ("Conflicting default implementations for " ++ pp f ++ ":") $$
                                                   vcat [ text "-" <+> multilineText (pp d) | d <- nub (x : xs) ]
  decls <- Map.traverseWithKey getUnique $ Map.unionsWith (<>) $ (map . fmap) (:| []) defaults

  -- TODO: order default implementations differently?
  return ([minPragma | not (null prims)] ++ Map.elems decls)

compileRecord :: RecordTarget -> Definition -> C (Hs.Decl ())
compileRecord target def = setCurrentRange (nameBindingSite $ qnameName $ defName def) $ do
  TelV tel _ <- telViewUpTo recPars (defType def)
  params <- compileTele tel
  addContext tel $ do
    pars <- mapM (showTCM . unArg) params
    let hd = foldl (\ h p -> Hs.DHApp () h (Hs.UnkindedVar () $ hsName p))
                   (Hs.DHead () (hsName rName))
                   pars
    let fieldTel = snd $ splitTelescopeAt recPars recTel
    case target of
      ToClass ms -> do
        (classConstraints, classDecls) <- compileRecFields classDecl recFields fieldTel
        let context = case classConstraints of
              []     -> Nothing
              [asst] -> Just (Hs.CxSingle () asst)
              assts  -> Just (Hs.CxTuple () assts)
        defaultDecls <- compileMinRecords def ms
        return $ Hs.ClassDecl () context hd [] (Just (classDecls ++ map (Hs.ClsDecl ()) defaultDecls))
      ToRecord -> do
        (constraints, fieldDecls) <- compileRecFields fieldDecl recFields fieldTel
        unless (null constraints) __IMPOSSIBLE__ -- no constraints for records
        mapM_ checkFieldInScope (map unDom recFields)
        let conDecl = Hs.QualConDecl () Nothing Nothing $ Hs.RecDecl () cName fieldDecls
        return $ Hs.DataDecl () (Hs.DataType ()) Nothing hd [conDecl] []

  where
    rName = prettyShow $ qnameName $ defName def
    cName | recNamedCon = hsName $ prettyShow $ qnameName $ conName recConHead
          | otherwise   = hsName rName   -- Reuse record name for constructor if no given name


    -- In Haskell, projections live in the same scope as the record type, so check here that the
    -- record module has been opened.
    checkFieldInScope f = isInScopeUnqualified f >>= \ case
      True  -> return ()
      False -> setCurrentRange (nameBindingSite $ qnameName f) $ genericError $
        "Record projections (`" ++ prettyShow (qnameName f) ++ "` in this case) must be brought into scope when compiling to Haskell record types. " ++
        "Add `open " ++ rName ++ " public` after the record declaration to fix this."

    Record{..} = theDef def

    classDecl :: Hs.Name () -> Hs.Type () -> Hs.ClassDecl ()
    classDecl n = Hs.ClsDecl () . Hs.TypeSig () [n]

    fieldDecl :: Hs.Name () -> Hs.Type () -> Hs.FieldDecl ()
    fieldDecl n = Hs.FieldDecl () [n]

    compileRecFields :: (Hs.Name () -> Hs.Type () -> b)
                     -> [Dom QName] -> Telescope -> C ([Hs.Asst ()], [b])
    compileRecFields decl ns tel = case (ns, tel) of
      (_   , EmptyTel          ) -> return ([], [])
      (n:ns, ExtendTel dom tel') -> do
        hsDom <- compileDom (absName tel') dom
        (hsAssts, hsFields) <- underAbstraction dom tel' $ compileRecFields decl ns
        case hsDom of
          DomType hsA -> do
            let fieldName = hsName $ prettyShow $ qnameName $ unDom n
            return (hsAssts, decl fieldName hsA : hsFields)
          DomConstraint hsA -> case target of
            ToClass{} -> return (hsA : hsAssts , hsFields)
            ToRecord{} -> genericError $
              "Not supported: record/class with constraint fields"
          DomDropped -> return (hsAssts , hsFields)
      (_, _) -> __IMPOSSIBLE__
