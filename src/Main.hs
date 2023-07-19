module Main where

import System.Console.GetOpt

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
defaultOptions = Options{ optOutDir = Nothing, optExtensions = [], rewriteRules = [] }

outdirOpt :: Monad m => FilePath -> Options -> m Options
outdirOpt dir opts = return opts{ optOutDir = Just dir }

extensionOpt :: Monad m => String -> Options -> m Options
extensionOpt ext opts = return opts{ optExtensions = Hs.parseExtension ext : optExtensions opts }

-- Here we use unsafePerformIO to read the rewrite rules from the files.
rewriteOpt :: Monad m => FilePath -> Options -> m Options
rewriteOpt file opts = return opts{
                         rewriteRules = UNSAFE.unsafePerformIO (readRewritesFromFile file)
                                          ++ rewriteRules opts}
{-# NOINLINE rewriteOpt #-}

backend :: Backend' Options Options ModuleEnv ModuleRes (CompiledDef, CompileOutput)
backend = Backend'
  { backendName           = "agda2hs"
  , backendVersion        = Just "1.0"
  , options               = defaultOptions
  , commandLineFlags      =
      [ Option ['o'] ["out-dir"] (ReqArg outdirOpt "DIR")
        "Write Haskell code to DIR. (default: project root)"
      , Option ['X'] [] (ReqArg extensionOpt "EXTENSION")
        "Enable Haskell language EXTENSION. Affects parsing of Haskell code in FOREIGN blocks."
      , Option [] ["rewrite-rules"] (ReqArg rewriteOpt "FILE")
        "Provide custom rewrite rules in a YAML configuration file. Identifiers contained here will be replaced with the one given, with an appropriate import added if requested. See rewrite-rules-example.yaml for the format."
      ]
  , isEnabled             = \ _ -> True
  , preCompile            = return
  , postCompile           = \ _ _ _ -> return ()
  , preModule             = moduleSetup
  , postModule            = writeModule
  , compileDef            = compile
  , scopeCheckingSuffices = False
  , mayEraseType          = \ _ -> return True
  }

main = runAgda [Backend backend]
