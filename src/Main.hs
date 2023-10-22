module Main where

import Control.Monad.IO.Class ( MonadIO(..) )

import System.Console.GetOpt
import System.Environment ( getArgs )

import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Build as Hs
import qualified Language.Haskell.Exts.Parser as Hs
import qualified Language.Haskell.Exts.Extension as Hs

import Agda.Main
import Agda.Compiler.Backend

import Agda2Hs.Compile
import Agda2Hs.Compile.Rewrites
import Agda2Hs.Compile.Types
import Agda2Hs.Render

import qualified System.IO.Unsafe as UNSAFE (unsafePerformIO)

defaultOptions :: Options
defaultOptions = Options{ optIsEnabled = True,
                          optOutDir = Nothing, optExtensions = [],
                          optPrelude = (False, Auto),   -- default to including Prelude explicitly and letting agda2hs search for identifiers to import automatically
                          optRewrites = [] }

disableOpt :: Monad m => Options -> m Options
disableOpt opts = return opts{ optIsEnabled = False }

outdirOpt :: Monad m => FilePath -> Options -> m Options
outdirOpt dir opts = return opts{ optOutDir = Just dir }

extensionOpt :: Monad m => String -> Options -> m Options
extensionOpt ext opts = return opts{ optExtensions = Hs.parseExtension ext : optExtensions opts }

-- Here we use unsafePerformIO to read the rewrite rules from the files.
rewriteOpt :: Monad m => FilePath -> Options -> m Options
rewriteOpt file opts = return opts{
                         optRewrites = newRules ++ optRewrites opts,
                         optPrelude = case maybePreludeOptions of {
                                   Nothing       -> optPrelude opts;
                                   Just newPOpts -> newPOpts
                                   -- ^ the new one trumps the older one
                                   -- maybe this should be done so that we are given an error in case of conflicting options
                                   }}
  where
    (maybePreludeOptions, newRules) = UNSAFE.unsafePerformIO (readConfigFile file)
{-# NOINLINE rewriteOpt #-}

backend :: Backend' Options Options ModuleEnv ModuleRes (CompiledDef, CompileOutput)
backend = Backend'
  { backendName           = "agda2hs"
  , backendVersion        = Just "1.0"
  , options               = defaultOptions
  , commandLineFlags      =
      [ Option ['d'] ["disable-backend"] (NoArg disableOpt)
        "Disable backend and fall back to vanilla Agda behaviour, without compilation (important for Emacs mode). Implied when run in interactive mode (with --interactive, --interaction or --interaction-json)."
      , Option ['o'] ["out-dir"] (ReqArg outdirOpt "DIR")
        "Write Haskell code to DIR. (default: project root)"
      , Option ['X'] [] (ReqArg extensionOpt "EXTENSION")
        "Enable Haskell language EXTENSION. Affects parsing of Haskell code in FOREIGN blocks."
      , Option [] ["rewrite-rules"] (ReqArg rewriteOpt "FILE")
        "Provide custom rewrite rules in a YAML configuration file. Identifiers contained here will be replaced with the one given, with an appropriate import added if requested. The handling of imports from Prelude should preferably also be included in this file. See rewrite-rules-example.yaml for the format."
      ]
  , isEnabled             = optIsEnabled
  , preCompile            = return
  , postCompile           = \ _ _ _ -> return ()
  , preModule             = moduleSetup
  , postModule            = writeModule
  , compileDef            = compile
  , scopeCheckingSuffices = False
  , mayEraseType          = \ _ -> return True
  }

-- Checking whether we are in interactive mode.
-- These will imply --disable-backend.
isInteractive :: IO Bool
isInteractive = do
  let interactionFlag = Option ['I'] ["interactive", "interaction", "interaction-json"] (NoArg ()) ""
  (i , _ , _) <- getOpt Permute [interactionFlag] <$> getArgs
  return $ not $ null i

main = do
  -- Issue #201: drop backend when run in interactive mode
  isInt <- isInteractive
  if isInt
    then runAgda [Backend (backend{isEnabled = const False})]
    else runAgda [Backend backend]
