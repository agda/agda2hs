module Agda2Hs.Render where

import Control.Monad ( unless )
import Control.Monad.IO.Class ( MonadIO(liftIO) )

import Data.Function ( on )
import Data.List ( sortBy, nub )
import Data.Maybe ( fromMaybe, isNothing )
import Data.Set ( Set )
import qualified Data.Set as Set

import System.FilePath ( takeDirectory )
import System.Directory ( createDirectoryIfMissing )

import qualified Language.Haskell.Exts.SrcLoc as Hs
import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Build as Hs
import qualified Language.Haskell.Exts.ExactPrint as Hs
import qualified Language.Haskell.Exts.Extension as Hs

import Agda.Compiler.Backend

import Agda.TypeChecking.Pretty
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Position
import Agda.Syntax.TopLevelModuleName
import Agda.Syntax.Common.Pretty ( prettyShow )

import Agda.Utils.Impossible ( __IMPOSSIBLE__ )

import Agda2Hs.Compile
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Imports
import Agda2Hs.Compile.Utils ( primModules, moduleFileName )
import Agda2Hs.HsUtils
import Agda2Hs.Pragma ( getForeignPragmas )

import Language.Haskell.Exts as Hs (prettyPrint, prelude_mod)

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

ensureDirectory :: FilePath -> IO ()
ensureDirectory = createDirectoryIfMissing True . takeDirectory

-- We have to rewrite this so that in the IThingAll and IThingWith import specs,
-- the "type" prefixes get before type operators if necessary.
-- But see haskell-src-exts, PR #475. If it gets merged, this will be unnecessary.
prettyShowImportDecl :: Hs.ImportDecl () -> String
prettyShowImportDecl (Hs.ImportDecl _ m qual src safe mbPkg mbName mbSpecs) =
  unwords $ ("import" :) $
            (if src  then ("{-# SOURCE #-}" :) else id) $
            (if safe then ("safe" :) else id) $
            (if qual then ("qualified" :) else id) $
            maybeAppend (\ str -> show str) mbPkg $
            (pp m :) $
            maybeAppend (\m' -> "as " ++ pp m') mbName $
            (case mbSpecs of {Just specs -> [prettyShowSpecList specs]; Nothing -> []})
    where
      maybeAppend :: (a -> String) -> Maybe a -> ([String] -> [String])
      maybeAppend f (Just a) = (f a :)
      maybeAppend _ Nothing  = id

      prettyShowSpecList :: Hs.ImportSpecList () -> String
      prettyShowSpecList (Hs.ImportSpecList _ b ispecs)  =
            (if b then "hiding " else "")
                ++ parenList (map prettyShowSpec ispecs)

      parenList :: [String] -> String
      parenList [] = ""
      parenList (x:xs) = '(' : (x ++ go xs)
        where
          go :: [String] -> String
          go [] = ")"
          go (x:xs) = ", " ++ x ++ go xs

      -- this is why we have rewritten it
      prettyShowSpec :: Hs.ImportSpec () -> String
      prettyShowSpec (Hs.IVar _ name  )        = pp name
      prettyShowSpec (Hs.IAbs _ ns name)       = let ppns = pp ns in case ppns of
          []                                  -> pp name -- then we don't write a space before it
          _                                   -> ppns ++ (' ' : pp name)
      prettyShowSpec (Hs.IThingAll _ name) = let rest = pp name ++ "(..)" in
        case name of
          -- if it's a symbol, append a "type" prefix to the beginning
          (Hs.Symbol _ _)                     -> pp (Hs.TypeNamespace ()) ++ (' ' : rest)
          (Hs.Ident  _ _)                     -> rest
      prettyShowSpec (Hs.IThingWith _ name nameList) = let rest = pp name ++ (parenList . map pp $ nameList) in
        case name of
          (Hs.Symbol _ _)                     -> pp (Hs.TypeNamespace ()) ++ (' ' : rest)
          (Hs.Ident  _ _)                     -> rest

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

    let unlines' [] = []
        unlines' ss = unlines ss ++ "\n"

    let preOpts@PreludeOpts{..} = optPrelude opts

    -- if the prelude is supposed to be implicit,
    -- or the prelude imports have been fixed in the config file,
    -- we remove it from the list of imports
    let filteredImps =
          if not preludeImplicit && isNothing preludeImports
            then imps
            else filter ((/= Hs.prelude_mod ()) . importModule) imps

    -- then we try to add it back
    let autoImportList =
          if (not preludeImplicit && isNothing preludeImports) || null preludeHiding
            then compileImports mod filteredImps
            else (preludeImportDecl preOpts:) <$> compileImports mod filteredImps

    -- Add automatic imports
    autoImports <- (unlines' . map prettyShowImportDecl) <$> autoImportList

    -- The comments make it hard to generate and pretty print a full module
    hsFile <- moduleFileName opts m

    let output = concat
          [ renderLangExts exts
          , renderBlocks $ codePragmas code
          , "module " ++ mod ++ " where\n\n"
          , autoImports
          , renderBlocks defs
          ]

    reportSLn "" 1 $ "Writing " ++ hsFile

    liftIO $ ensureDirectory hsFile >> writeFile hsFile output
