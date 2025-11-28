{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Exception (catch, SomeException)
import Control.Monad (forM, unless)
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Lazy.Char8 as LBS8
import Data.List (intercalate, isPrefixOf, isSuffixOf, sort)
import System.Directory
  ( doesFileExist
  , getCurrentDirectory
  , listDirectory
  , removeFile
  , setCurrentDirectory
  )
import System.Exit (ExitCode(..))
import System.FilePath ((</>), dropExtension, makeRelative, takeDirectory, takeFileName)
import System.Process (readProcessWithExitCode)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Golden (goldenVsStringDiff)

main :: IO ()
main = do
  -- Discover the test directory path (relative to the current working directory)
  cwd <- getCurrentDirectory
  let testDir = cwd </> "test"

  -- Change to the test directory so that agda2hs can find the agda-lib
  setCurrentDirectory testDir

  -- Discover test cases
  succeedTests <- discoverSucceedTests testDir
  failTests <- discoverFailTests testDir

  -- Run tests
  defaultMain $ testGroup "agda2hs"
    [ testGroup "Succeed" succeedTests
    , testGroup "Fail" failTests
    ]

-- | Discover all .agda files under the Succeed directory recursively.
discoverSucceedTests :: FilePath -> IO [TestTree]
discoverSucceedTests testDir = do
  agdaFiles <- findAgdaFilesRecursive (testDir </> "Succeed")
  forM (sort agdaFiles) $ \agdaFile -> do
    let relPath = makeRelative testDir agdaFile
        testName = dropExtension (makeRelative (testDir </> "Succeed") agdaFile)
        goldenFile = dropExtension agdaFile ++ ".hs"
    return $ succeedTest testName relPath goldenFile

-- | Discover all .agda files under the Fail directory.
discoverFailTests :: FilePath -> IO [TestTree]
discoverFailTests testDir = do
  agdaFiles <- findAgdaFilesRecursive (testDir </> "Fail")
  forM (sort agdaFiles) $ \agdaFile -> do
    let relPath = makeRelative testDir agdaFile
        testName = dropExtension (makeRelative (testDir </> "Fail") agdaFile)
        goldenFile = dropExtension agdaFile ++ ".err"
    return $ failTest testName relPath goldenFile

-- | Find all .agda files recursively in a directory.
findAgdaFilesRecursive :: FilePath -> IO [FilePath]
findAgdaFilesRecursive dir = do
  contents <- listDirectory dir
  paths <- forM contents $ \name -> do
    let path = dir </> name
    isDir <- doesDirectoryExist path
    if isDir
      then findAgdaFilesRecursive path
      else return [path | ".agda" `isSuffixOf` name]
  return (concat paths)

-- | Check if path is a directory.
doesDirectoryExist :: FilePath -> IO Bool
doesDirectoryExist path = do
  exists <- doesFileExist path
  if exists
    then return False
    else do
      -- If it's not a file, check if it's a directory
      contents <- listDirectory path `catch` \(_ :: SomeException) -> return []
      return (not (null contents) || path `elem` ["Succeed", "Fail", "Cubical"])

-- | Create a test for a succeed case.
-- Runs agda2hs on the .agda file, compares the output .hs to the golden file,
-- then compiles the .hs file with ghc.
succeedTest :: String -> FilePath -> FilePath -> TestTree
succeedTest testName agdaFile goldenFile =
  goldenVsStringDiff testName diffCmd goldenFile $ do
    -- Get the output directory (same as the agda file directory)
    let outDir = takeDirectory agdaFile

    -- Run agda2hs
    (exitCode, stdout, stderr) <- readProcessWithExitCode
      "agda2hs"
      [agdaFile, "-o", outDir, "-v0"]
      ""

    case exitCode of
      ExitSuccess -> do
        -- Read the generated .hs file
        let generatedFile = dropExtension agdaFile ++ ".hs"
        content <- LBS.readFile generatedFile

        -- Also run ghc to check the generated code compiles
        (ghcExit, ghcOut, ghcErr) <- readProcessWithExitCode
          "ghc"
          ["-fno-code", generatedFile]
          ""

        case ghcExit of
          ExitSuccess -> return content
          ExitFailure _ -> return $ LBS8.pack $
            "GHC compilation failed:\n" ++ ghcOut ++ ghcErr

      ExitFailure _ -> return $ LBS8.pack $
        "agda2hs failed:\n" ++ stdout ++ stderr

-- | Create a test for a fail case.
-- Runs agda2hs on the .agda file, expects it to fail, and compares the error
-- message to the golden file.
failTest :: String -> FilePath -> FilePath -> TestTree
failTest testName agdaFile goldenFile =
  goldenVsStringDiff testName diffCmd goldenFile $ do
    -- Run agda2hs (expecting failure)
    (exitCode, stdout, stderr) <- readProcessWithExitCode
      "agda2hs"
      [agdaFile, "-o", takeDirectory agdaFile, "-v0"]
      ""

    let output = stdout ++ stderr
        -- Relativize paths in the output
        relativizedOutput = relativizePaths output

    case exitCode of
      ExitSuccess ->
        return $ LBS8.pack "UNEXPECTED SUCCESS"
      ExitFailure _ ->
        return $ LBS8.pack relativizedOutput

-- | Relativize absolute paths in error messages.
-- This replaces absolute paths with relative paths to make tests portable.
relativizePaths :: String -> String
relativizePaths = unlines . map relativizeLine . lines
  where
    relativizeLine line =
      -- Look for patterns like /path/to/test/Foo.agda:line:col
      -- and replace with test/Foo.agda:line:col or just Foo.agda:line:col
      case break (== '/') line of
        (prefix, '/':rest) ->
          if "test/" `isInfixOf` rest || "Fail/" `isInfixOf` rest || "Succeed/" `isInfixOf` rest
            then prefix ++ extractRelativePath rest
            else line
        _ -> line

    extractRelativePath :: String -> String
    extractRelativePath path =
      -- Find "test/" in the path and take from there
      case findTestPrefix path of
        Just relPath -> relPath
        Nothing -> path

    findTestPrefix :: String -> Maybe String
    findTestPrefix s
      | "test/" `isPrefixOf` s = Just s
      | null s = Nothing
      | otherwise = findTestPrefix (drop 1 s)

    isInfixOf :: String -> String -> Bool
    isInfixOf needle haystack = any (isPrefixOf needle) (tails haystack)

    tails :: String -> [String]
    tails [] = [[]]
    tails s@(_:xs) = s : tails xs

-- | Diff command for golden tests.
diffCmd :: FilePath -> FilePath -> [String]
diffCmd ref new = ["diff", "-u", ref, new]
