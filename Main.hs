module Main where

import Control.Monad
import Control.Monad.Fail (MonadFail)
import Control.Monad.IO.Class
import Data.List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import System.Console.GetOpt
import System.Environment

import Agda.Main (runAgda)
import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.BasicOps
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.Syntax.Common
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
compile' def =
  case theDef def of
    Function{} -> compileFun r hsName def
    _          -> return []
  where x = qnameName $ defName def
        r = nameBindingSite x
        hsName = prettyShow x

compileClause :: String -> Clause -> TCM String
compileClause x c = return $ x ++ " = undefined"

paren True  s = "(" ++ s ++ ")"
paren False s = s

data PrimType = Nat | List | Unit
  deriving (Show, Eq)

type Builtins = Map QName PrimType

getBuiltins :: TCM Builtins
getBuiltins = Map.fromList . concat <$> mapM getB [(builtinNat, Nat), (builtinList, List), (builtinUnit, Unit)]
  where
    getB (b, t) = getBuiltin' b >>= \ case
      Nothing        -> return []
      Just (Def q _) -> return [(q, t)]

renderPrimType :: PrimType -> [String] -> String
renderPrimType Nat  []  = "Integer"
renderPrimType List [a] = "[" ++ a ++ "]"
renderPrimType Unit []  = "()"

compileType :: Builtins -> Int -> Term -> TCM String
compileType builtins p t = do
  t <- reduce t
  case t of
    Pi a b | hidden a -> underAbstraction a b (compileType builtins p . unEl)
             -- Hidden Pi means Haskell forall
    Pi a (NoAbs _ b) | visible a -> do
      hsA <- compileType builtins 1 (unEl $ unDom a)
      hsB <- compileType builtins 0 (unEl b)
      return $ paren (p > 0) (hsA ++ " -> " ++ hsB)
    Def f es | Just prim <- Map.lookup f builtins
             , Just args <- allApplyElims es -> do
      vs <- mapM (compileType builtins 0 . unArg) $ filter visible args
      return $ renderPrimType prim vs
    t@(Var _ []) -> show <$> prettyTCM t
    t -> genericDocError =<< text "Bad Haskell type:" <?> prettyTCM t

compileFun :: Range -> String -> Definition -> TCM CompiledDef
compileFun r x def = do
  builtins <- getBuiltins
  ty <- compileType builtins 0 (unEl $ defType def)
  cs <- mapM (compileClause x) funClauses
  let code = x ++ " :: " ++ ty ++ "\n" ++
             unlines cs
  return [(r, code)]
  where
    Function{..} = theDef def

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

