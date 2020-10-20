module Main where

import Control.Monad
import Control.Monad.Fail (MonadFail)
import Control.Monad.IO.Class
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import System.Console.GetOpt
import System.Environment

import Agda.Main (runAgda)
import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.BasicOps
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.Syntax.Internal hiding (sort, set)
import Agda.Syntax.Position
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.TheTypeChecker
import Agda.TypeChecking.Rules.Term (isType_)
import Agda.TypeChecking.Reduce
import Agda.Interaction.CommandLine (withCurrentFile)
import Agda.Utils.Lens
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.FileName

data Options = Options { }

defaultOptions :: Options
defaultOptions = Options{}

pragmaName :: String
pragmaName = "AGDA2HS"

type Env         = ()
type ModuleEnv   = ()
type ModuleRes   = ()
type CompiledDef = [(Range, String)]

backend :: Backend' Options Env ModuleEnv ModuleRes CompiledDef
backend = Backend'
  { backendName           = "agda2hs"
  , backendVersion        = Just "0.1"
  , options               = defaultOptions
  , commandLineFlags      = []
  , isEnabled             = \ _ -> True
  , preCompile            = \ _ -> return ()
  , postCompile           = \ _ _ _ -> return ()
  , preModule             = \ _ _ _ _ -> return (Recompile ())
  , postModule            = writeModule
  , compileDef            = compile
  , scopeCheckingSuffices = False
  , mayEraseType          = \ _ -> return True
  }

getPreamble :: TCM [(Range, String)]
getPreamble = reverse . map getCode . fromMaybe [] . Map.lookup pragmaName . iForeignCode <$> curIF
  where getCode (ForeignCode r code) = (r, code ++ "\n")

compile :: Env -> ModuleEnv -> IsMain -> Definition -> TCM CompiledDef
compile _ _ _ def = getUniqueCompilerPragma pragmaName (defName def) >>= \ case
  Nothing -> return []
  Just _  -> compile' def

compile' :: Definition -> TCM CompiledDef
compile' def = return [(nameBindingSite x, prettyShow x ++ " = undefined\n")]
  where x = qnameName $ defName def

renderCode :: [(Range, String)] -> String
renderCode = unlines . map snd . sort

writeModule :: Env -> ModuleEnv -> IsMain -> ModuleName -> [CompiledDef] -> TCM ModuleRes
writeModule _ _ isMain m defs = do
  preamble <- getPreamble
  case preamble ++ concat defs of
    []   -> return ()
    defs -> liftIO $ do
      putStrLn $ "module " ++ prettyShow m ++ " where\n"
      putStrLn $ renderCode defs

main = runAgda [Backend backend]

