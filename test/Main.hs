module Main where

import Control.Monad (forM)
import qualified Data.ByteString.Lazy as LBS
import Data.List (isPrefixOf, isSuffixOf, isInfixOf, sortBy)
import Data.Ord (Down(..), comparing)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Time.Clock (UTCTime)
import System.Directory
  ( createDirectoryIfMissing
  , doesDirectoryExist
  , doesFileExist
  , getCurrentDirectory
  , getModificationTime
  , getTemporaryDirectory
  , listDirectory
  , setCurrentDirectory
  )
import System.Exit (ExitCode(..))
import System.FilePath ((</>), dropExtension, makeRelative, takeDirectory)
import System.Process (readProcessWithExitCode)
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
  createDirectoryIfMissing True buildDir

  -- Discover test cases
  succeedTests <- discoverSucceedTests testDir buildDir
  failTests <- discoverFailTests testDir buildDir

  -- Run tests
  defaultMain $ testGroup "agda2hs"
    [ testGroup "Succeed" succeedTests
    , testGroup "Fail" failTests
    ]

-- | Discover all .agda files under the Succeed directory recursively.
-- Files are ordered by: modification date (newest first), then golden value
-- modification date (newest first), then alphabetically.
discoverSucceedTests :: FilePath -> FilePath -> IO [TestTree]
discoverSucceedTests testDir buildDir = do
  agdaFiles <- findAgdaFilesRecursive (testDir </> "Succeed")
  sortedFiles <- sortByModTime agdaFiles (\f -> dropExtension f ++ ".hs")
  forM sortedFiles $ \agdaFile -> do
    let testName = dropExtension (makeRelative (testDir </> "Succeed") agdaFile)
        goldenFile = dropExtension agdaFile ++ ".hs"
    return $ succeedTest testDir buildDir testName agdaFile goldenFile

-- | Discover all .agda files under the Fail directory.
-- Files are ordered by: modification date (newest first), then golden value
-- modification date (newest first), then alphabetically.
discoverFailTests :: FilePath -> FilePath -> IO [TestTree]
discoverFailTests testDir buildDir = do
  agdaFiles <- findAgdaFilesRecursive (testDir </> "Fail")
  sortedFiles <- sortByModTime agdaFiles (\f -> dropExtension f ++ ".err")
  forM sortedFiles $ \agdaFile -> do
    let testName = dropExtension (makeRelative (testDir </> "Fail") agdaFile)
        goldenFile = dropExtension agdaFile ++ ".err"
    return $ failTest testDir buildDir testName agdaFile goldenFile

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
    return (f, agdaTime, goldenTime)
  return $ map (\(f,_,_) -> f) $ sortBy fileOrder filesWithTimes
  where
    fileOrder (f1, t1, g1) (f2, t2, g2) =
      -- First by agda file modification time (newest first)
      case comparing Down t1 t2 of
        EQ -> case (g1, g2) of
          -- Then by golden file modification time (newest first)
          (Just gt1, Just gt2) -> case comparing Down gt1 gt2 of
            EQ -> compare f1 f2  -- Finally alphabetically
            x  -> x
          (Just _, Nothing) -> LT
          (Nothing, Just _) -> GT
          (Nothing, Nothing) -> compare f1 f2
        x -> x

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
    (exitCode, stdout, stderr) <- readProcessWithExitCode
      "agda2hs"
      [agdaFile, "-o", outDir, "-v0", "-i" ++ succeedDir]
      ""

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
    (exitCode, stdout, stderr) <- readProcessWithExitCode
      "agda2hs"
      [agdaFile, "-o", outDir, "-v0", "-i" ++ failDir, "-i" ++ succeedDir]
      ""

    let output = stdout ++ stderr
        -- Relativize paths in the output
        relativizedOutput = relativizePaths output

    case exitCode of
      ExitSuccess ->
        return $ stringToLBS "UNEXPECTED SUCCESS"
      ExitFailure _ ->
        return $ stringToLBS relativizedOutput

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

-- | Diff command for golden tests.
diffCmd :: FilePath -> FilePath -> [String]
diffCmd ref new = ["diff", "-u", ref, new]
