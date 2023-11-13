module Main where

import Data.Maybe ( fromMaybe )
import Data.Version ( showVersion )
import Control.Monad.IO.Class ( MonadIO(liftIO) )

import System.Console.GetOpt
import System.Environment ( getArgs )

import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Build as Hs
import qualified Language.Haskell.Exts.Parser as Hs
import qualified Language.Haskell.Exts.Extension as Hs

import Agda.Main
import Agda.Compiler.Backend

import Agda2Hs.Compile.Name ( defaultSpecialRules )
import Agda2Hs.Compile
import Agda2Hs.Config ( checkConfig )
import Agda2Hs.Compile.Types
import Agda2Hs.Render

import Paths_agda2hs ( version )

defaultOptions :: Options
defaultOptions = Options
  { optIsEnabled = True
  , optOutDir = Nothing
  , optConfigFile = Nothing
  , optExtensions = []
  , optPrelude = PreludeOpts False Nothing []
    -- by default the Prelude is imported explicitly
  , optRewrites = defaultSpecialRules
  }

disableOpt :: Monad m => Options -> m Options
disableOpt opts = return opts{ optIsEnabled = False }

outdirOpt :: Monad m => FilePath -> Options -> m Options
outdirOpt dir opts = return opts{ optOutDir = Just dir }

configOpt :: Monad m => FilePath -> Options -> m Options
configOpt src opts = return opts{optConfigFile = Just src}

extensionOpt :: Monad m => String -> Options -> m Options
extensionOpt ext opts = return opts{ optExtensions = Hs.parseExtension ext : optExtensions opts }

-- | Update options by reading the config, if any was specified.

backend :: Backend' Options Options ModuleEnv ModuleRes (CompiledDef, CompileOutput)
backend = Backend'
  { backendName           = "agda2hs"
  , backendVersion        = Just (showVersion version)
  , options               = defaultOptions
  , commandLineFlags      =
      [ Option ['d'] ["disable-backend"] (NoArg disableOpt)
        "Disable backend and fall back to vanilla Agda behaviour, without compilation (important for Emacs mode). Implied when run in interactive mode (with --interactive, --interaction or --interaction-json)."
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
  , postModule            = writeModule
  , compileDef            = compile
  , scopeCheckingSuffices = False
  , mayEraseType          = \ _ -> return True
  }

-- | Parse command-line arguments to check whether we are in interactive mode.
isInteractive :: IO Bool
isInteractive = do
  let interactionFlag = Option ['I'] ["interactive", "interaction", "interaction-json"] (NoArg ()) ""
  (i , _ , _) <- getOpt Permute [interactionFlag] <$> getArgs
  return $ not $ null i

main = do
  -- Issue #201: disable backend when run in interactive mode
  isInt <- isInteractive
  if isInt
    then runAgda [Backend backend{isEnabled = const False}]
    else runAgda [Backend backend]
