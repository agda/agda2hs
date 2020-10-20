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
import Agda.Syntax.Literal
import Agda.Syntax.Internal hiding (sort, set)
import Agda.Syntax.Position
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.TheTypeChecker
import Agda.TypeChecking.Rules.Term (isType_)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute hiding (sort)
import Agda.TypeChecking.Telescope
import Agda.Interaction.CommandLine (withCurrentFile)
import Agda.Utils.Lens
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.FileName
import Agda.Utils.List

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

showTCM :: PrettyTCM a => a -> TCM String
showTCM x = show <$> prettyTCM x

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
    Datatype{} -> compileData r hsName def
    _          -> return []
  where x = qnameName $ defName def
        r = nameBindingSite x
        hsName = prettyShow x

compileData :: Range -> String -> Definition -> TCM CompiledDef
compileData r d def = do
  case theDef def of
    Datatype{dataPars = n, dataIxs = 0, dataCons = cs} -> do
      TelV tel _ <- telViewUpTo n (defType def)
      addContext tel $ do
        let params = teleArgs tel :: [Arg Term]
        pars <- mapM (showTCM . unArg) $ filter visible params
        cs   <- mapM (compileConstructor params) cs
        return [(r, "data " ++ d ++ concatMap (" " ++) pars ++ "\n" ++
                       concat (zipWith (\ bar c -> "  " ++ bar ++ " " ++ c ++ "\n")
                                       ("=" : repeat "|") cs))]

compileConstructor :: [Arg Term] -> QName -> TCM String
compileConstructor params c = do
  ty <- (`piApplyM` params) . defType =<< getConstInfo c
  TelV tel _ <- telView ty
  c <- showTCM c
  args <- compileConstructorArgs tel
  return $ c ++ concatMap (" " ++) args

compileConstructorArgs :: Telescope -> TCM [String]
compileConstructorArgs EmptyTel = return []
compileConstructorArgs (ExtendTel a tel)
  | visible a, NoAbs _ tel <- reAbs tel = do
    builtins <- getBuiltins
    (:) <$> compileType builtins 1 (unEl $ unDom a) <*> compileConstructorArgs tel
compileConstructorArgs tel = genericDocError =<< text "Bad constructor args:" <?> prettyTCM tel

compileClause :: String -> Clause -> TCM String
compileClause x Clause{clauseTel       = tel,
                       namedClausePats = ps,
                       clauseBody      = body } =
  addContext tel $ do
    ps   <- compilePats ps
    body <- maybe (return "undefined") (compileTerm 0) body
    return $ x ++ " " ++ unwords ps ++ " = " ++ body

renderCon :: QName -> [String] -> TCM String
renderCon c args = do
  c <- showTCM c
  return $ renderApp 1 c args

renderApp :: Int -> String -> [String] -> String
renderApp _ h     []      = h
renderApp p "_∷_" [x, xs] = paren (p > 0) $ x ++ " : " ++ xs
renderApp p h [a, b] | Just op <- isInfix h = paren (p > 0) $ a ++ " " ++ op ++ " " ++ b
renderApp p h     ps      = paren (p > 0) $ h ++ " " ++ unwords ps
-- TODO: error on weird mixfix operators

isInfix :: String -> Maybe String
isInfix ('_' : f) = do
  (op, '_') <- initLast f
  return op
isInfix _ = Nothing

compilePats :: NAPs -> TCM [String]
compilePats ps = mapM (compilePat . namedArg) $ filter visible ps

compilePat :: DeBruijnPattern -> TCM String
compilePat p@(VarP _ _)  = showTCM p
compilePat (ConP h _ ps) = do
  ps <- compilePats ps
  renderCon (conName h) ps
-- LitP
compilePat p = genericDocError =<< text "bad pattern:" <?> prettyTCM p

compileTerm :: Int -> Term -> TCM String
compileTerm p v =
  case unSpine v of
    Var x es -> (`app` es) =<< showTCM (Var x [])
    Def f es -> (`app` es) =<< showTCM (Def f [])
    Con h i es -> (`app` es) =<< showTCM (Con h i [])
    Lit (LitNat n) -> return (show n)
    t -> genericDocError =<< text "bad term:" <?> prettyTCM t
  where
    app :: String -> Elims -> TCM String
    app s es = do
      let Just args = allApplyElims es
      args <- mapM (compileTerm 1 . unArg) $ filter visible args
      return $ renderApp p s args

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

renderTypeVar :: String -> TCM String
renderTypeVar = return    -- TODO: check stuff

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
    Def f es | Just args <- allApplyElims es -> do
      vs <- mapM (compileType builtins 0 . unArg) $ filter visible args
      f <- showTCM f
      return $ renderApp p f vs
    t@(Var _ []) -> renderTypeVar =<< showTCM t
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

