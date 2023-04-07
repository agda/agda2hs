module Main where

import System.Console.GetOpt

import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Build as Hs
import qualified Language.Haskell.Exts.Parser as Hs
import qualified Language.Haskell.Exts.Extension as Hs

import Agda.Main
import Agda.Compiler.Backend

import Agda2Hs.Compile
import Agda2Hs.Compile.Types
import Agda2Hs.Render

defaultOptions :: Options
defaultOptions = Options{ optOutDir = Nothing, optExtensions = [] }

outdirOpt :: Monad m => FilePath -> Options -> m Options
outdirOpt dir opts = return opts{ optOutDir = Just dir }

extensionOpt :: Monad m => String -> Options -> m Options
extensionOpt ext opts = return opts{ optExtensions = Hs.parseExtension ext : optExtensions opts }

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
