module Main where

import Data.Maybe ( fromMaybe )
import qualified Data.Text as Text
import Data.Version ( showVersion )
import Control.Monad.IO.Class ( MonadIO(liftIO) )

import System.Environment ( getArgs )

import Agda.Main
import Agda.Compiler.Backend
import Agda.Utils.GetOpt

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Name ( defaultSpecialRules )
import Agda2Hs.Compile
import Agda2Hs.Config ( checkConfig )
import Agda2Hs.Compile.Types
import Agda2Hs.Render

import qualified Agda2Hs.Language.Haskell as Hs

import Paths_agda2hs ( version, getDataFileName )


-- | Agda2Hs default config
defaultOptions :: Options
defaultOptions = Options
  { optIsEnabled  = True
  , optOutDir     = Nothing
  , optConfigFile = Nothing
  , optExtensions = []
  , optPrelude    = PreludeOpts False Nothing []
    -- by default the Prelude is imported explicitly
  , optRewrites   = defaultSpecialRules
  }


disableOpt :: Flag Options
disableOpt opts = return opts { optIsEnabled = False }

outdirOpt :: FilePath -> Flag Options
outdirOpt dir opts = return opts { optOutDir = Just dir }

configOpt :: FilePath -> Flag Options
configOpt src opts = return opts { optConfigFile = Just src }

extensionOpt :: String -> Flag Options
extensionOpt ext opts = return opts { optExtensions = Hs.parseExtension ext : optExtensions opts }


backend :: Backend' Options Options ModuleEnv ModuleRes (CompiledDef, CompileOutput)
backend = Backend'
  { backendName           = "agda2hs"
  , backendVersion        = Just $ Text.pack $ showVersion version
  , options               = defaultOptions
  , commandLineFlags      =
      [ Option ['d'] ["disable-backend"] (NoArg disableOpt)
          "Disable backend and fall back to vanilla Agda behaviour, \
          \without compilation (important for Emacs mode). \
          \Implied when run in interactive mode (with --interactive, --interaction or --interaction-json)."
      , Option ['o'] ["out-dir"] (ReqArg outdirOpt "DIR")
          "Write Haskell code to DIR. (default: project root)"
      , Option ['X'] [] (ReqArg extensionOpt "EXTENSION")
          "Enable Haskell language EXTENSION. Affects parsing of Haskell code in FOREIGN blocks."
      , Option [] ["config"] (ReqArg configOpt "FILE")
          "Provide additional configuration to agda2hs with a YAML file."
      ]
  , isEnabled             = optIsEnabled
  , preCompile            = checkConfig
  , postCompile           = \ _ _ _ -> return ()
  , preModule             = moduleSetup
  , postModule            = verifyAndWriteModule
  , compileDef            = compile
  , scopeCheckingSuffices = False
  , mayEraseType          = \ _ -> return True
  , backendInteractTop    = Nothing
  , backendInteractHole   = Nothing
  }
  where
    verifyAndWriteModule opts env isM m out = verifyOutput opts env isM m out >> writeModule opts env isM m out

-- | Parse command-line arguments to check whether we are in interactive mode
--   or the user is just requesting information.
shouldDisable :: IO Bool
shouldDisable = do
  let interactionFlag = Option ['I'] ["interactive", "interaction", "interaction-json"] (NoArg ()) ""
  (i , _ , _) <- getOpt Permute (interactionFlag:infoFlags) <$> getArgs
  return $ not $ null i

main = do
  args <- getArgs

  -- Issue #370: `agda2hs locate` will print out the path to the prelude agda-lib file
  if args == ["locate"] then
    putStrLn =<< getDataFileName "lib/base/base.agda-lib"
  else do
    -- Issue #201: disable backend when run in interactive mode
    disable <- shouldDisable

    runAgda [Backend backend{isEnabled = const $ not disable }]
