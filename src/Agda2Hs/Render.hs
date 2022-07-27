module Agda2Hs.Render where

import Control.Applicative
import Control.Arrow ((>>>), (***), (&&&), first, second)
import Control.Monad
import Control.Monad.Error
import Control.Monad.Fail (MonadFail)
import Control.Monad.Reader
import Control.Monad.IO.Class
import Control.DeepSeq
import Data.Data
import Data.Generics (mkT, everywhere, listify, extT, everything, mkQ, Data)
import Data.Function
import Data.List
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as List1
import Data.Maybe
import Data.Map (Map)
import qualified Data.Text as Text
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap
import Data.Set (Set)
import qualified Data.Set as Set
import System.Console.GetOpt
import System.Environment
import System.FilePath
import System.Directory

import qualified Language.Haskell.Exts.SrcLoc     as Hs
import qualified Language.Haskell.Exts.Syntax     as Hs
import qualified Language.Haskell.Exts.Build      as Hs
import qualified Language.Haskell.Exts.Pretty     as Hs
import qualified Language.Haskell.Exts.Parser     as Hs
import qualified Language.Haskell.Exts.ExactPrint as Hs
import qualified Language.Haskell.Exts.Extension  as Hs
import qualified Language.Haskell.Exts.Comments   as Hs

import Agda.Main (runAgda)
import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.BasicOps
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty hiding (pretty)
import Agda.Syntax.Common hiding (Ranged)
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Translation.ConcreteToAbstract hiding (topLevelModuleName)
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad hiding (withCurrentModule)
import Agda.TheTypeChecker
import Agda.TypeChecking.CheckInternal (infer)
import Agda.TypeChecking.Constraints (noConstraints)
import Agda.TypeChecking.Conversion (equalTerm)
import Agda.TypeChecking.Free
import Agda.TypeChecking.InstanceArguments (findInstance)
import Agda.TypeChecking.Level (isLevelType)
import Agda.TypeChecking.MetaVars (newInstanceMeta)
import Agda.TypeChecking.Rules.Term (isType_)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Records
import Agda.TypeChecking.Sort
import Agda.Utils.Lens
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.FileName
import Agda.Utils.List
import Agda.Utils.Impossible
import Agda.Utils.Maybe.Strict (toLazy, toStrict)
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Functor

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Types
import Agda2Hs.HsUtils
import Agda2Hs.Pragma

-- Rendering --------------------------------------------------------------

type Block = Ranged [String]

sortRanges :: [Ranged a] -> [a]
sortRanges = map snd . sortBy (compare `on` rLine . fst)

rLine :: Range -> Int
rLine r = fromIntegral $ fromMaybe 0 $ posLine <$> rStart r

renderBlocks :: [Block] -> String
renderBlocks = unlines . map unlines . sortRanges . filter (not . null . snd)

defBlock :: CompiledDef -> [Block]
defBlock def = [ (r, map (pp . insertParens) ds) | (r, ds) <- def ]

codePragmas :: [Ranged Code] -> [Block]
codePragmas code = [ (r, map pp ps) | (r, (Hs.Module _ _ ps _ _, _)) <- code ]

codeBlocks :: [Ranged Code] -> [Block]
codeBlocks code = [(r, [uncurry Hs.exactPrint $ moveToTop $ noPragmas mcs]) | (r, mcs) <- code, nonempty mcs]
  where noPragmas (Hs.Module l h _ is ds, cs) = (Hs.Module l h [] is ds, cs)
        noPragmas m                           = m
        nonempty (Hs.Module _ _ _ is ds, cs) = not $ null is && null ds && null cs
        nonempty _                           = True

-- Checking imports -------------------------------------------------------

imports :: [Ranged Code] -> [Hs.ImportDecl Hs.SrcSpanInfo]
imports modules = concat [imps | (_, (Hs.Module _ _ _ imps _, _)) <- modules]

autoImports :: [(String, String)]
autoImports = [("Natural", "Numeric.Natural")]

addImports :: [Hs.ImportDecl Hs.SrcSpanInfo] -> [CompiledDef] -> TCM [Hs.ImportDecl ()]
addImports is defs = do
  return [ doImport ty imp | (ty, imp) <- autoImports,
                             uses ty defs && not (any (isImport ty imp) is)]
  where
    doImport :: String -> String -> Hs.ImportDecl ()
    doImport ty imp = Hs.ImportDecl ()
      (Hs.ModuleName () imp) False False False Nothing Nothing
      (Just $ Hs.ImportSpecList () False [Hs.IVar () $ Hs.name ty])

    isImport :: String -> String -> Hs.ImportDecl Hs.SrcSpanInfo -> Bool
    isImport ty imp = \case
      Hs.ImportDecl _ (Hs.ModuleName _ m) False _ _ _ _ specs | m == imp ->
        case specs of
          Just (Hs.ImportSpecList _ hiding specs) ->
            not hiding && ty `elem` concatMap getExplicitImports specs
          Nothing -> True
      _ -> False

checkImports :: [Hs.ImportDecl Hs.SrcSpanInfo] -> TCM ()
checkImports is = do
  case concatMap checkImport is of
    []  -> return ()
    bad@((r, _, _):_) -> setCurrentRange r $
      genericDocError =<< vcat
        [ text "Bad import of builtin type"
        , nest 2 $ vcat [ text $ ty ++ " from module " ++ m ++ " (expected " ++ okm ++ ")"
                        | (_, m, ty) <- bad, let Just okm = lookup ty autoImports ]
        , text "Note: imports of builtin types are inserted automatically if omitted."
        ]

checkImport :: Hs.ImportDecl Hs.SrcSpanInfo -> [(Range, String, String)]
checkImport i
  | Just (Hs.ImportSpecList _ False specs) <- Hs.importSpecs i =
    [ (r, mname, ty) | (r, ty) <- concatMap (checkImportSpec mname) specs ]
  | otherwise = []
  where
    mname = pp (Hs.importModule i)
    checkImportSpec :: String -> Hs.ImportSpec Hs.SrcSpanInfo -> [(Range, String)]
    checkImportSpec mname = \case
      Hs.IVar       loc   n    -> check loc n
      Hs.IAbs       loc _ n    -> check loc n
      Hs.IThingAll  loc   n    -> check loc n
      Hs.IThingWith loc   n ns -> concat $ check loc n : map check' ns
      where
        check' cn = check (cloc cn) (cname cn)
        check loc n = [(srcSpanInfoToRange loc, s) | let s = pp n, badImp s]
        badImp s = maybe False (/= mname) $ lookup s autoImports

-- Generating the files -------------------------------------------------------

moduleFileName :: Options -> ModuleName -> FilePath
moduleFileName opts name =
  optOutDir opts </> C.moduleNameToFileName (toTopLevelModuleName name) "hs"

moduleSetup :: Options -> IsMain -> ModuleName -> filepath -> TCM (Recompile ModuleEnv ModuleRes)
moduleSetup _ _ m _ = do
  reportSDoc "agda2hs.compile" 3 $ text "Compiling module: " <+> prettyTCM m
  setScope . iInsideScope =<< curIF
  return $ Recompile m

ensureDirectory :: FilePath -> IO ()
ensureDirectory = createDirectoryIfMissing True . takeDirectory

writeModule :: Options -> ModuleEnv -> IsMain -> ModuleName -> [CompiledDef] -> TCM ModuleRes
writeModule opts _ isMain m defs0 = do
  code <- getForeignPragmas (optExtensions opts)
  let defs = concatMap defBlock defs0 ++ codeBlocks code
  let imps = imports code
  unless (null code && null defs) $ do
    -- Check user-supplied imports
    checkImports imps
    -- Add automatic imports for builtin types (if any)
    let unlines' [] = []
        unlines' ss = unlines ss ++ "\n"
    autoImports <- unlines' . map pp <$> addImports imps defs0
    -- The comments makes it hard to generate and pretty print a full module
    let hsFile = moduleFileName opts m
        output = concat
                 [ renderBlocks $ codePragmas code
                 , "module " ++ prettyShow m ++ " where\n\n"
                 , autoImports
                 , renderBlocks defs ]
    reportSLn "" 1 $ "Writing " ++ hsFile
    liftIO $ ensureDirectory hsFile
    liftIO $ writeFile hsFile output
