module Agda2Hs.Render where

import Control.Monad ( unless )
import Control.Monad.Except ( MonadIO(liftIO) )

import Data.Function ( on )
import Data.List ( sortBy, nub )
import Data.Maybe ( fromMaybe )
import Data.Set ( Set )
import qualified Data.Set as Set

import System.FilePath ( takeDirectory, (</>) )
import System.Directory ( createDirectoryIfMissing )

import qualified Language.Haskell.Exts.SrcLoc as Hs
import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Build as Hs
import qualified Language.Haskell.Exts.ExactPrint as Hs
import qualified Language.Haskell.Exts.Extension as Hs

import Agda.Compiler.Backend
import Agda.Compiler.Common ( curIF, compileDir )

import Agda.TypeChecking.Pretty
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Position
import Agda.Syntax.TopLevelModuleName

import Agda.Utils.Pretty ( prettyShow )
import Agda2Hs.Compile
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Imports
import Agda2Hs.HsUtils
import Agda2Hs.Pragma ( getForeignPragmas )

-- Rendering --------------------------------------------------------------

type Block = Ranged [String]

sortRanges :: [Ranged a] -> [a]
sortRanges = map snd . sortBy (compare `on` rLine . fst)

rLine :: Range -> Int
rLine r = fromIntegral $ fromMaybe 0 $ posLine <$> rStart r

renderBlocks :: [Block] -> String
renderBlocks = unlines . map unlines . sortRanges . filter (not . null . snd)

defBlock :: [Ranged [Hs.Decl ()]] -> [Block]
defBlock def = [ (r, map (pp . insertParens) ds) | (r, ds) <- def ]

renderLangExts :: [Hs.KnownExtension] -> String
renderLangExts exts
  | null exts = ""
  | otherwise = pp (Hs.LanguagePragma () $ nub $ map extToName exts) ++ "\n"

codePragmas :: [Ranged Code] -> [Block]
codePragmas code = [ (r, map pp ps) | (r, (Hs.Module _ _ ps _ _, _)) <- code ]

codeBlocks :: [Ranged Code] -> [Block]
codeBlocks code = [(r, [uncurry Hs.exactPrint $ moveToTop $ noPragmas mcs]) | (r, mcs) <- code, nonempty mcs]
  where noPragmas (Hs.Module l h _ is ds, cs) = (Hs.Module l h [] is ds, cs)
        noPragmas m                           = m
        nonempty (Hs.Module _ _ _ is ds, cs) = not $ null is && null ds && null cs
        nonempty _                           = True

-- Generating the files -------------------------------------------------------

moduleFileName :: Options -> TopLevelModuleName -> TCM FilePath
moduleFileName opts name = do
  outDir <- compileDir
  return $ fromMaybe outDir (optOutDir opts) </> moduleNameToFileName name "hs"

moduleSetup :: Options -> IsMain -> TopLevelModuleName -> Maybe FilePath -> TCM (Recompile ModuleEnv ModuleRes)
moduleSetup _ _ m _ = do
  reportSDoc "agda2hs.compile" 3 $ text "Compiling module: " <+> prettyTCM m
  setScope . iInsideScope =<< curIF
  return $ Recompile m

ensureDirectory :: FilePath -> IO ()
ensureDirectory = createDirectoryIfMissing True . takeDirectory

writeModule :: Options -> ModuleEnv -> IsMain -> TopLevelModuleName
            -> [(CompiledDef, CompileOutput)] -> TCM ModuleRes
writeModule opts _ isMain m outs = do
  code <- getForeignPragmas (optExtensions opts)
  let mod  = prettyShow m
      (cdefs, impss, extss) = unzip3 $ flip map outs $
        \(cdef, CompileOutput imps exts) -> (cdef, imps, exts)
      defs = concatMap defBlock cdefs ++ codeBlocks code
      imps = concat impss
      exts = concat extss
  unless (null code && null defs && isMain == NotMain) $ do
    -- Add automatic imports
    let unlines' [] = []
        unlines' ss = unlines ss ++ "\n"
    autoImports <- unlines' . map pp <$> compileImports mod imps
    -- The comments makes it hard to generate and pretty print a full module
    hsFile <- moduleFileName opts m
    let output = concat
                 [ renderLangExts exts
                 , renderBlocks $ codePragmas code
                 , "module " ++ mod ++ " where\n\n"
                 , autoImports
                 , renderBlocks defs ]
    reportSLn "" 1 $ "Writing " ++ hsFile
    liftIO $ ensureDirectory hsFile >> writeFile hsFile output
