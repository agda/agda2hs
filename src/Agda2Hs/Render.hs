{-# LANGUAGE OverloadedStrings #-}

module Agda2Hs.Render where

import Control.Monad ( when, unless )
import Control.Monad.IO.Class ( MonadIO(liftIO) )

import Data.Function ( on )
import Data.List ( intercalate, sortBy, nub, unzip5 )
import Data.Maybe ( fromMaybe, isNothing )
import Data.Set ( Set )
import qualified Data.Set as Set

import System.FilePath ( takeDirectory, takeBaseName, joinPath, (</>) )
import System.Directory ( createDirectoryIfMissing )

import Agda.Compiler.Backend
import Agda.Compiler.Common ( compileDir )

import Agda.TypeChecking.Pretty
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Position
import Agda.Syntax.TopLevelModuleName
import Agda.Syntax.Common.Pretty ( prettyShow )

import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import qualified Agda.Utils.List1 as List1

import Agda2Hs.Compile
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Imports
import Agda2Hs.Compile.Utils ( primModules )
import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils
  ( extToName, pp, moveToTop, insertParens )
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


ensureDirectory :: FilePath -> IO ()
ensureDirectory = createDirectoryIfMissing True . takeDirectory

-- | Compile the full import list,
-- with special handling for the @Prelude@ as prescribed by 'Options'.
compileImportsWithPrelude
  :: Options -> String -> Imports -> TCM [Hs.ImportDecl ()]
compileImportsWithPrelude opts mod imps = do
    -- if the prelude is supposed to be implicit,
    -- or the prelude imports have been fixed in the config file,
    -- we remove it from the list of imports
    let filteredImps =
          if not preludeImplicit && isNothing preludeImports
            then imps
            else filter ((/= Hs.prelude_mod ()) . importModule) imps

    -- then we try to add it back
    if (not preludeImplicit && isNothing preludeImports) || null preludeHiding
      then compileImports mod filteredImps
      else (preludeImportDecl preOpts:) <$> compileImports mod filteredImps
  where
    preOpts@PreludeOpts{..} = optPrelude opts


-- | Render the @.hs@ module as a 'String' and write it to a file.
writeModule :: Options -> ModuleEnv -> IsMain -> TopLevelModuleName
            -> [(RtcDefs, CompileOutput)] -> TCM ModuleRes
writeModule opts _ isMain m outs = do
  code <- getForeignPragmas (optExtensions opts)
  let mod = prettyShow m
      (cdefs, impss, extss, sfs, chkds) = unzip5 $ flip map outs $
          \(cdef, CompileOutput imps exts ne achk ) -> (cdef, imps, exts, ne, achk)
      defs = concatMap (defBlock . defn ) cdefs ++ codeBlocks code
      chkdefs = concatMap (defBlock . rtcDefn ) cdefs
      imps = concat impss
      exts = concat extss
      safe = concat sfs
      chkd = map prettyShow $ concat chkds
  unless (null code && null defs && isMain == NotMain) $ do

    let unlines' [] = []
        unlines' ss = unlines ss ++ "\n"

    autoImports <- unlines' . map Hs.prettyShowImportDecl
      <$> compileImportsWithPrelude opts mod imps

    let preOpts@PreludeOpts{..} = optPrelude opts
        nameParts = rawModuleNameParts $ rawTopLevelModuleName m
        rtc = optRtc opts && List1.head nameParts `notElem` ["Agda", "Haskell"]

    -- The comments make it hard to generate and pretty print a full module
    hsFile <- moduleFileName opts m
    when (rtc && "PostRtc" `elem` List1.toList nameParts) $ do
      genericDocError =<< ("Illegal module name" <+> prettyTCM m)
        <> ", conflicts with name generated for runtime checks."
    let postFile = joinPath [takeDirectory hsFile, takeBaseName hsFile, "PostRtc.hs"]
        renderedExps = intercalate ", " $ safe ++ chkd

    -- "pre" runtime check output (_the_ output if RTC disabled)
    let preOutput = concat
          [ "module " ++ mod ++ " (" ++ renderedExps ++ ") where\n\n"
          , autoImports
          , "import " ++ mod ++ ".PostRtc\n\n"
          , renderBlocks chkdefs
          ]
        output = concat
          [ renderLangExts exts
          , renderBlocks $ codePragmas code
          , "module " ++ mod ++ (if rtc then ".PostRtc" else "") ++ " where\n\n"
          , autoImports
          , renderBlocks defs
          ]

    reportSLn "" 1 $ "Writing " ++ hsFile
    liftIO $ ensureDirectory hsFile >> writeFile hsFile (if rtc then preOutput else output)
    when rtc $ do
      reportSLn "" 1 $ "Writing " ++ postFile
      liftIO $ ensureDirectory postFile >> writeFile postFile output
