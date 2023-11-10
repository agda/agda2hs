{-# LANGUAGE NamedFieldPuns #-}
module Agda2Hs.Compile.Record where

import Control.Monad ( unless )
import Control.Monad.Reader ( MonadReader(local) )

import Data.List ( (\\), nub )
import Data.List.NonEmpty ( NonEmpty(..) )
import Data.Map ( Map )
import qualified Data.Map as Map

import qualified Language.Haskell.Exts as Hs

import Agda.Compiler.Backend

import Agda.Syntax.Common ( Arg(unArg), defaultArg )
import Agda.Syntax.Internal
import Agda.Syntax.Common.Pretty ( prettyShow )

import Agda.TypeChecking.Pretty ( ($$), (<+>), text, vcat )
import Agda.TypeChecking.Substitute ( TelV(TelV), Apply(apply) )
import Agda.TypeChecking.Telescope

import Agda.Utils.Impossible ( __IMPOSSIBLE__ )

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.ClassInstance
import Agda2Hs.Compile.Function ( compileFun )
import Agda2Hs.Compile.Type ( compileDom, compileTeleBinds )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils

-- | Primitive fields and default implementations
type MinRecord = ([Hs.Name ()], Map (Hs.Name ()) (Hs.Decl ()))

withMinRecord :: QName -> C a -> C a
withMinRecord m = local $ \ e -> e { minRecordName = Just (qnameToMName m) }

compileMinRecord :: [Hs.Name ()] -> QName -> C MinRecord
compileMinRecord fieldNames m = do
  rdef <- getConstInfo m
  definedFields <- classMemberNames rdef
  let Record{recPars = npars, recTel = tel} = theDef rdef
      pars = map Apply $ take npars $ teleArgs tel
      rtype = El __DUMMY_SORT__ $ Def m pars
  defaults <- lookupDefaultImplementations m (fieldNames \\ definedFields)
  -- We can't simply compileFun here for two reasons:
  -- * it has an explicit dictionary argument
  -- * it's using the fields and definitions from the minimal record and not the parent record
  compiled <- withMinRecord m $ addContext (defaultDom rtype) $
    fmap concat $ traverse (compileFun False) defaults
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
        | otherwise     = genericDocError =<< do
          text ("Conflicting default implementations for " ++ pp f ++ ":") $$
            vcat [ text "-" <+> multilineText (pp d) | d <- nub (x : xs) ]
  decls <- Map.traverseWithKey getUnique
         $ Map.unionsWith (<>) $ (map . fmap) (:| []) defaults

  -- TODO: order default implementations differently?
  return ([minPragma | not (null prims)] ++ Map.elems decls)

compileRecord :: RecordTarget -> Definition -> C (Hs.Decl ())
compileRecord target def = do
  TelV tel _ <- telViewUpTo recPars (defType def)
  addContext tel $ checkingVars $ do
    checkValidTypeName rName
    binds <- compileTeleBinds tel
    let hd = foldl (Hs.DHApp ()) (Hs.DHead () rName) binds
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
      ToRecord ds -> do
        checkValidConName cName
        (constraints, fieldDecls) <- compileRecFields fieldDecl recFields fieldTel
        compileDataRecord constraints fieldDecls (Hs.DataType ()) hd ds
      ToRecordNewType ds -> do
        checkValidConName cName
        (constraints, fieldDecls) <- compileRecFields fieldDecl recFields fieldTel
        checkSingleElement cName fieldDecls "Newtype must have exactly one field in constructor"
        compileDataRecord constraints fieldDecls (Hs.NewType ()) hd ds

  where
    rName = hsName $ prettyShow $ qnameName $ defName def
    cName | recNamedCon = hsName $ prettyShow $ qnameName $ conName recConHead
          | otherwise   = rName   -- Reuse record name for constructor if no given name

    -- In Haskell, projections live in the same scope as the record type, so check here that the
    -- record module has been opened.
    checkFieldInScope f = isInScopeUnqualified f >>= \case
      True  -> return ()
      False -> setCurrentRangeQ f $ genericError $
        "Record projections (`" ++ prettyShow (qnameName f) ++
        "` in this case) must be brought into scope when compiling to Haskell record types. " ++
        "Add `open " ++ Hs.prettyPrint rName ++ " public` after the record declaration to fix this."

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
          DomType s hsA -> do
            let fieldName = hsName $ prettyShow $ qnameName $ unDom n
            fieldType <- addTyBang s hsA
            checkValidFunName fieldName
            return (hsAssts, decl fieldName fieldType : hsFields)
          DomConstraint hsA -> case target of
            ToClass{} -> return (hsA : hsAssts , hsFields)
            ToRecord{} -> genericError $
              "Not supported: record/class with constraint fields"
          DomDropped -> return (hsAssts , hsFields)
      (_, _) -> __IMPOSSIBLE__

    compileDataRecord :: [Hs.Asst ()] -> [Hs.FieldDecl ()] -- compiled rec fields
                         -> Hs.DataOrNew () -- whether to compile to data or newtype
                         -> Hs.DeclHead () -- the head of the type declaration
                         -> [Hs.Deriving ()] -- data extracted from the pragma
                         -> C (Hs.Decl ())
    compileDataRecord constraints fieldDecls don hd ds = do
      unless (null constraints) __IMPOSSIBLE__ -- no constraints for records
      mapM_ checkFieldInScope (map unDom recFields)
      let conDecl = Hs.QualConDecl () Nothing Nothing $ Hs.RecDecl () cName fieldDecls
      return $ Hs.DataDecl () don Nothing hd [conDecl] ds

checkUnboxPragma :: Defn -> C ()
checkUnboxPragma def
  | Record{recFields} <- def
  , length (filter keepArg recFields) == 1
  , not (recRecursive def)
  = return ()

  | otherwise
  = genericError "An unboxed type must be a non-recursive record type with exactly one non-erased field."
