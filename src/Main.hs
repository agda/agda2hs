module Main where

import System.Console.GetOpt ( ArgDescr(ReqArg), OptDescr(Option) )
import Agda.Main ( runAgda )
import Agda.Compiler.Backend ( Backend(Backend), Backend'(..) )
import Agda2Hs.Compile
    ( defaultOptions, outdirOpt, extensionOpt, compile )
import Agda2Hs.Compile.Types
    ( Options, CompiledDef, ModuleRes, ModuleEnv )
import Agda2Hs.Render ( moduleSetup, writeModule )

backend :: Backend' Options Options ModuleEnv ModuleRes CompiledDef
backend = Backend'
  { backendName           = "agda2hs"
  , backendVersion        = Just "0.1"
  , options               = defaultOptions
  , commandLineFlags      = [ Option ['o'] ["out-dir"] (ReqArg outdirOpt "DIR")
                              "Write Haskell code to DIR. Default: ."
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
