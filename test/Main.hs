module Main where

import Control.Monad (forM, filterM)
import qualified Data.ByteString.Lazy as LBS
import Data.List (isPrefixOf, isSuffixOf, isInfixOf, sort)
import Data.Maybe (catMaybes)
import Data.Ord (Down(..))
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import System.Directory
  ( createDirectoryIfMissing
  , doesDirectoryExist
  , doesFileExist
  , getCurrentDirectory
  , getModificationTime
  , getTemporaryDirectory
  , listDirectory
  , removeFile
  , removePathForcibly
  , setCurrentDirectory
  )
import System.Exit (ExitCode(..))
import System.FilePath ((</>), dropExtension, makeRelative, takeDirectory)
import System.Process
  ( CreateProcess(..)
  , proc
  , readCreateProcessWithExitCode
  , readProcessWithExitCode
  )
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Golden (goldenVsStringDiff)

-- | Convert a String to a lazy ByteString using UTF-8 encoding.
stringToLBS :: String -> LBS.ByteString
stringToLBS = LBS.fromStrict . TE.encodeUtf8 . T.pack

main :: IO ()
main = do
  -- Discover the test directory path (relative to the current working directory)
  cwd <- getCurrentDirectory
  let testDir = cwd </> "test"

  -- Change to the test directory so that agda2hs can find the agda-lib
  setCurrentDirectory testDir

  -- Create a temporary build directory
  tmpDir <- getTemporaryDirectory
  let buildDir = tmpDir </> "agda2hs-test-build"
  removePathForcibly buildDir
  createDirectoryIfMissing True buildDir

  -- Discover test cases
  succeedTests <- discoverSucceedTests testDir buildDir
  failTests <- discoverFailTests testDir buildDir
  customTests <- discoverIncrementalTests testDir buildDir

  -- Run tests
  defaultMain $ testGroup "agda2hs"
    [ testGroup "Succeed" succeedTests
    , testGroup "Fail" failTests
    , testGroup "Custom" customTests
    ]

-- | Discover all .agda files under the Succeed directory recursively.
-- Files are ordered by: modification date (newest first), then golden value
-- modification date (newest first), then alphabetically.
discoverSucceedTests :: FilePath -> FilePath -> IO [TestTree]
discoverSucceedTests testDir buildDir =
  discoverTests testDir buildDir "Succeed" ".hs" succeedTest

-- | Discover all .agda files under the Fail directory.
-- Files are ordered by: modification date (newest first), then golden value
-- modification date (newest first), then alphabetically.
discoverFailTests :: FilePath -> FilePath -> IO [TestTree]
discoverFailTests testDir buildDir =
  discoverTests testDir buildDir "Fail" ".err" failTest

-- | Discover incremental tests under the Incremental directory.
-- A test is an @<Name>.agda@ file that has a matching golden @<Name>.hs@.
-- Other @.agda@ files in the directory are treated as helper modules and are
-- not run as tests directly. The golden file is the output of a clean
-- compilation; the test recompiles the module after deleting only its output,
-- forcing its dependencies to be skipped, and checks that the regenerated
-- output still matches the golden file (see Issue #486).
discoverIncrementalTests :: FilePath -> FilePath -> IO [TestTree]
discoverIncrementalTests testDir buildDir = do
  let dir = testDir </> "Incremental"
  agdaFiles <- findAgdaFiles dir
  tests <- forM agdaFiles $ \agdaFile -> do
    let goldenFile = dropExtension agdaFile ++ ".hs"
    hasGolden <- doesFileExist goldenFile
    if hasGolden
      then do
        let testName = dropExtension (makeRelative dir agdaFile)
        return $ Just $ incrementalTest testDir buildDir testName agdaFile goldenFile
      else return Nothing
  return $ catMaybes tests

-- | Generic test discovery function.
-- Takes the directory name, golden file extension, and test function.
discoverTests :: FilePath -> FilePath -> String -> String
              -> (FilePath -> FilePath -> String -> FilePath -> FilePath -> TestTree)
              -> IO [TestTree]
discoverTests testDir buildDir dirName goldenExt testFn = do
  let dir = testDir </> dirName
  agdaFiles <- findAgdaFiles dir
  sortedFiles <- sortByModTime agdaFiles (\f -> dropExtension f ++ goldenExt)
  forM sortedFiles $ \agdaFile -> do
    let testName = dropExtension (makeRelative dir agdaFile)
        goldenFile = dropExtension agdaFile ++ goldenExt
    return $ testFn testDir buildDir testName agdaFile goldenFile

-- | Sort files by modification time (newest first), then by golden value
-- modification time (if it exists), then alphabetically.
sortByModTime :: [FilePath] -> (FilePath -> FilePath) -> IO [FilePath]
sortByModTime files goldenPath = do
  filesWithTimes <- forM files $ \f -> do
    agdaTime <- getModificationTime f
    let golden = goldenPath f
    goldenExists <- doesFileExist golden
    goldenTime <- if goldenExists
                    then Just <$> getModificationTime golden
                    else return Nothing
    -- Use Down to sort newest first; standard tuple ordering does the rest
    return (Down agdaTime, Down goldenTime, f)
  return $ map (\(_,_,f) -> f) $ sort filesWithTimes

-- | Find all .agda files recursively in a directory.
findAgdaFiles :: FilePath -> IO [FilePath]
findAgdaFiles dir = do
  entries <- listDirectory dir
  let paths = map (dir </>) entries
  files <- filterM doesFileExist paths
  dirs <- filterM doesDirectoryExist paths
  let agdaFiles = filter (".agda" `isSuffixOf`) files
  subFiles <- concat <$> mapM findAgdaFiles dirs
  return $ agdaFiles ++ subFiles

-- | Create a test for a succeed case.
-- Runs agda2hs on the .agda file, compares the output .hs to the golden file,
-- then compiles the .hs file with ghc.
succeedTest :: FilePath -> FilePath -> String -> FilePath -> FilePath -> TestTree
succeedTest testDir buildDir testName agdaFile goldenFile =
  goldenVsStringDiff testName diffCmd goldenFile $ do
    let succeedDir = testDir </> "Succeed"
        -- Output to build directory to avoid polluting source tree
        outDir = buildDir </> "Succeed"
        -- Get the relative path from Succeed to the agda file
        relAgdaPath = makeRelative succeedDir agdaFile
        -- Compute the expected output file path (same relative path, but .hs)
        generatedFile = outDir </> dropExtension relAgdaPath ++ ".hs"
        generatedDir = takeDirectory generatedFile

    -- Ensure output directory exists (including subdirectories)
    createDirectoryIfMissing True generatedDir

    -- Run agda2hs with include path for Succeed directory
    (exitCode, stdout, stderr) <- runAgda2Hs succeedDir
      [agdaFile, "-o", outDir, "-v0", "-i" ++ succeedDir]

    case exitCode of
      ExitSuccess -> do
        -- Also run ghc to check the generated code compiles
        -- Add include path for finding imported modules
        (ghcExit, ghcOut, ghcErr) <- readProcessWithExitCode
          "ghc"
          ["-fno-code", "-i" ++ outDir, generatedFile]
          ""

        case ghcExit of
          -- The generated .hs file is the golden value
          ExitSuccess -> LBS.readFile generatedFile
          ExitFailure _ -> return $ stringToLBS $
            "GHC compilation failed:\n" ++ ghcOut ++ ghcErr

      ExitFailure _ -> return $ stringToLBS $
        "agda2hs failed:\n" ++ stdout ++ stderr

-- | Create a test for a fail case.
-- Runs agda2hs on the .agda file, expects it to fail, and compares the error
-- message to the golden file.
failTest :: FilePath -> FilePath -> String -> FilePath -> FilePath -> TestTree
failTest testDir buildDir testName agdaFile goldenFile =
  goldenVsStringDiff testName diffCmd goldenFile $ do
    let failDir = testDir </> "Fail"
        succeedDir = testDir </> "Succeed"
        -- Output to build directory to avoid polluting source tree
        outDir = buildDir </> "Fail"

    -- Ensure output directory exists
    createDirectoryIfMissing True outDir

    -- Run agda2hs (expecting failure) with include paths for both directories
    -- Fail tests may depend on modules from Succeed
    (exitCode, stdout, stderr) <- runAgda2Hs failDir
      [agdaFile, "-o", outDir, "-v0", "-i" ++ failDir, "-i" ++ succeedDir]

    let output = stdout ++ stderr
        -- Relativize paths in the output
        relativizedOutput = relativizePaths output

    case exitCode of
      ExitSuccess ->
        return $ stringToLBS "UNEXPECTED SUCCESS"
      ExitFailure _ ->
        return $ stringToLBS relativizedOutput

-- | Create a test for an incremental compilation scenario (Issue #486).
-- First compiles the module from scratch, then deletes only its output so that
-- it is recompiled while its dependencies are considered up-to-date (and thus
-- skipped). The regenerated output must still match the clean output.
incrementalTest :: FilePath -> FilePath -> String -> FilePath -> FilePath -> TestTree
incrementalTest testDir buildDir testName agdaFile goldenFile =
  goldenVsStringDiff testName diffCmd goldenFile $ do
    let incrDir = testDir </> "Incremental"
        -- Output to build directory to avoid polluting source tree
        outDir = buildDir </> "Incremental"

    createDirectoryIfMissing True outDir

    -- First, compile from scratch so that both this module and its
    -- dependencies are generated and their interface files are written.
    (exitCode1, stdout1, stderr1) <- runAgda2Hs incrDir
      [agdaFile, "-o", outDir, "-v0", "-i" ++ incrDir]
    case exitCode1 of
      ExitFailure _ -> return $ stringToLBS $
        "agda2hs (clean) failed:\n" ++ stdout1 ++ stderr1
      ExitSuccess -> do
        let generatedFile = outDir </> dropExtension (makeRelative incrDir agdaFile) ++ ".hs"
        -- Delete only this module's output. Its dependencies keep their output
        -- and interface files, so they will be skipped on the next run.
        removeFile generatedFile
        -- Recompile. This module is rebuilt; its dependencies are skipped.
        (exitCode2, stdout2, stderr2) <- runAgda2Hs incrDir
          [agdaFile, "-o", outDir, "-v0", "-i" ++ incrDir]
        case exitCode2 of
          ExitFailure _ -> return $ stringToLBS $
            "agda2hs (incremental) failed:\n" ++ stdout2 ++ stderr2
          ExitSuccess   -> LBS.readFile generatedFile

-- | Run agda2hs from the test project's directory so Agda picks up the
-- corresponding per-directory .agda-lib file. Include paths alone do not
-- select a project library.
runAgda2Hs :: FilePath -> [String] -> IO (ExitCode, String, String)
runAgda2Hs cwd args =
  readCreateProcessWithExitCode ((proc "agda2hs" args) { cwd = Just cwd }) ""

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
          if any (`isInfixOf` rest) ["test/", "Fail/", "Succeed/"]
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
      | otherwise = case break (== '/') s of
          (_, '/':rest) -> findTestPrefix rest
          _ -> Nothing

-- | Diff command for golden tests.
diffCmd :: FilePath -> FilePath -> [String]
diffCmd ref new = ["diff", "-u", ref, new]
