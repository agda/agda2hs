module Main where

import Control.Monad
import Control.Monad.Fail (MonadFail)
import Control.Monad.IO.Class
import Data.Function
import Data.List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import System.Console.GetOpt
import System.Environment
import System.FilePath
import System.Directory

import qualified Language.Haskell.Exts.SrcLoc     as Hs
import qualified Language.Haskell.Exts.Syntax     as Hs
import qualified Language.Haskell.Exts.Pretty     as Hs
import qualified Language.Haskell.Exts.Parser     as Hs
import qualified Language.Haskell.Exts.ExactPrint as Hs
import qualified Language.Haskell.Exts.Comments   as Hs

import Agda.Main (runAgda)
import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.BasicOps
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty hiding (pretty)
import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.TheTypeChecker
import Agda.TypeChecking.Rules.Term (isType_)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.Interaction.CommandLine (withCurrentFile)
import Agda.Utils.Lens
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.FileName
import Agda.Utils.List
import Agda.Utils.Impossible
import Agda.Utils.Maybe.Strict (toLazy, toStrict)

data Options = Options { outDir :: FilePath }

defaultOptions :: Options
defaultOptions = Options{ outDir = "." }

outdirOpt :: Monad m => FilePath -> Options -> m Options
outdirOpt dir opts = return opts{ outDir = dir }

pragmaName :: String
pragmaName = "AGDA2HS"

type ModuleEnv   = Builtins
type ModuleRes   = ()
type CompiledDef = [(Range, [Hs.Decl ()])]

backend :: Backend' Options Options ModuleEnv ModuleRes CompiledDef
backend = Backend'
  { backendName           = "agda2hs"
  , backendVersion        = Just "0.1"
  , options               = defaultOptions
  , commandLineFlags      = [ Option ['o'] ["out-dir"] (ReqArg outdirOpt "DIR")
                              "Write Haskell code to DIR. Default: ." ]
  , isEnabled             = \ _ -> True
  , preCompile            = return
  , postCompile           = \ _ _ _ -> return ()
  , preModule             = moduleSetup
  , postModule            = writeModule
  , compileDef            = compile
  , scopeCheckingSuffices = False
  , mayEraseType          = \ _ -> return True
  }

-- Names ------------------------------------------------------------------

showTCM :: PrettyTCM a => a -> TCM String
showTCM x = show <$> prettyTCM x

isInfix :: String -> Maybe String
isInfix ('_' : f) = do
  (op, '_') <- initLast f
  return op
isInfix _ = Nothing

hsName :: String -> Hs.Name ()
hsName x
  | Just op <- isInfix x = Hs.Symbol () op
  | otherwise            = Hs.Ident () x

hsQName :: Builtins -> QName -> TCM (Hs.QName ())
hsQName builtins f
  | Just p <- Map.lookup f builtins = return $ compilePrim p
  | otherwise = do
    s <- showTCM f
    return $
      case break (== '.') $ reverse s of
        (_, "")        -> Hs.UnQual () (hsName s)
        (fr, _ : mr) -> Hs.Qual () (Hs.ModuleName () $ reverse mr) (hsName $ reverse fr)

isOp :: Hs.QName () -> Bool
isOp (Hs.UnQual _ Hs.Symbol{}) = True
isOp (Hs.Special _ Hs.Cons{})  = True
isOp _                         = False

-- Builtins ---------------------------------------------------------------

data Prim = Nat | List | Unit | Cons | Nil
  deriving (Show, Eq)

type Builtins = Map QName Prim

getBuiltins :: TCM Builtins
getBuiltins = Map.fromList . concat <$> mapM getB
                [ (builtinNat,  Nat)
                , (builtinList, List)
                , (builtinUnit, Unit)
                , (builtinCons, Cons)
                , (builtinNil,  Nil)
                ]
  where
    getB (b, t) = getBuiltin' b >>= \ case
      Nothing          -> return []
      Just (Def q _)   -> return [(q, t)]
      Just (Con c _ _) -> return [(conName c, t)]
      Just _           -> __IMPOSSIBLE__

compilePrim :: Prim -> Hs.QName ()
compilePrim Nat  = Hs.UnQual () (hsName "Integer")
compilePrim List = Hs.Special () (Hs.ListCon ())
compilePrim Unit = Hs.Special () (Hs.UnitCon ())
compilePrim Cons = Hs.Special () (Hs.Cons ())
compilePrim Nil  = Hs.Special () (Hs.ListCon ())

-- Compiling things -------------------------------------------------------

compile :: Options -> Builtins -> IsMain -> Definition -> TCM CompiledDef
compile _ builtins _ def = getUniqueCompilerPragma pragmaName (defName def) >>= \ case
  Nothing -> return []
  Just _  -> compile' builtins def

compile' :: Builtins -> Definition -> TCM CompiledDef
compile' builtins def =
  case theDef def of
    Function{} -> tag <$> compileFun builtins def
    Datatype{} -> tag <$> compileData builtins def
    _          -> return []
  where tag code = [(nameBindingSite $ qnameName $ defName def, code)]

compileData :: Builtins -> Definition -> TCM [Hs.Decl ()]
compileData builtins def = do
  let d = hsName $ prettyShow $ qnameName $ defName def
  case theDef def of
    Datatype{dataPars = n, dataIxs = 0, dataCons = cs} -> do
      TelV tel _ <- telViewUpTo n (defType def)
      addContext tel $ do
        let params = teleArgs tel :: [Arg Term]
        pars <- mapM (showTCM . unArg) $ filter visible params
        cs   <- mapM (compileConstructor builtins params) cs
        let hd   = foldl (\ h p -> Hs.DHApp () h (Hs.UnkindedVar () $ hsName p))
                         (Hs.DHead () d) pars
        return [Hs.DataDecl () (Hs.DataType ()) Nothing hd cs []]
    _ -> __IMPOSSIBLE__

compileConstructor :: Builtins -> [Arg Term] -> QName -> TCM (Hs.QualConDecl ())
compileConstructor builtins params c = do
  ty <- (`piApplyM` params) . defType =<< getConstInfo c
  TelV tel _ <- telView ty
  c <- showTCM c
  args <- compileConstructorArgs builtins tel
  return $ Hs.QualConDecl () Nothing Nothing $ Hs.ConDecl () (hsName c) args

compileConstructorArgs :: Builtins -> Telescope -> TCM [Hs.Type ()]
compileConstructorArgs _ EmptyTel = return []
compileConstructorArgs builtins (ExtendTel a tel)
  | visible a, NoAbs _ tel <- reAbs tel = do
    (:) <$> compileType builtins (unEl $ unDom a) <*> compileConstructorArgs builtins tel
compileConstructorArgs _ tel = genericDocError =<< text "Bad constructor args:" <?> prettyTCM tel

compileFun :: Builtins -> Definition -> TCM [Hs.Decl ()]
compileFun builtins def = do
  let x = hsName $ prettyShow $ qnameName $ defName def
  ty <- compileType builtins (unEl $ defType def)
  cs <- mapM (compileClause x) funClauses
  return [Hs.TypeSig () [x] ty, Hs.FunBind () cs]
  where
    Function{..} = theDef def

compileClause :: Hs.Name () -> Clause -> TCM (Hs.Match ())
compileClause x Clause{clauseTel       = tel,
                       namedClausePats = ps,
                       clauseBody      = body } =
  addContext tel $ do
    builtins <- getBuiltins
    ps   <- compilePats builtins ps
    body <- maybe (return $ Hs.Var () $ Hs.UnQual () (hsName "undefined")) (compileTerm builtins) body
    let rhs = Hs.UnGuardedRhs () body
    case (x, ps) of
      (Hs.Symbol{}, p : q : ps) -> return $ Hs.InfixMatch () p x (q : ps) rhs Nothing
      _                         -> return $ Hs.Match () x ps rhs Nothing

compileType :: Builtins -> Term -> TCM (Hs.Type ())
compileType builtins t = do
  t <- reduce t
  case t of
    Pi a b | hidden a -> underAbstraction a b (compileType builtins . unEl)
             -- Hidden Pi means Haskell forall
    Pi a (NoAbs _ b) | visible a -> do
      hsA <- compileType builtins (unEl $ unDom a)
      hsB <- compileType builtins (unEl b)
      return $ Hs.TyFun () hsA hsB
    Def f es | Just args <- allApplyElims es -> do
      vs <- mapM (compileType builtins . unArg) $ filter visible args
      f <- hsQName builtins f
      return $ tApp (Hs.TyCon () f) vs
    Var x es | Just args <- allApplyElims es -> do
      vs <- mapM (compileType builtins . unArg) $ filter visible args
      x  <- hsName <$> showTCM (Var x [])
      return $ tApp (Hs.TyVar () x) vs
    t -> genericDocError =<< text "Bad Haskell type:" <?> prettyTCM t

compileTerm :: Builtins -> Term -> TCM (Hs.Exp ())
compileTerm builtins v =
  case unSpine v of
    Var x es   -> (`app` es) . Hs.Var () . Hs.UnQual () . hsName =<< showTCM (Var x [])
    Def f es   -> (`app` es) . Hs.Var () =<< hsQName builtins f
    Con h i es -> (`app` es) . Hs.Con () =<< hsQName builtins (conName h)
    Lit (LitNat _ n) -> return $ Hs.Lit () $ Hs.Int () n (show n)
    Lam v b | visible v -> hsLambda (absName b) <$> underAbstraction_ b (compileTerm builtins)
    Lam _ b -> underAbstraction_ b (compileTerm builtins)
    t -> genericDocError =<< text "bad term:" <?> prettyTCM t
  where
    app :: Hs.Exp () -> Elims -> TCM (Hs.Exp ())
    app hd es = do
      let Just args = allApplyElims es
      args <- mapM (compileTerm builtins . unArg) $ filter visible args
      return $ eApp hd args

compilePats :: Builtins -> NAPs -> TCM [Hs.Pat ()]
compilePats builtins ps = mapM (compilePat builtins . namedArg) $ filter visible ps

compilePat :: Builtins -> DeBruijnPattern -> TCM (Hs.Pat ())
compilePat builtins p@(VarP _ _)  = Hs.PVar () . hsName <$> showTCM p
compilePat builtins (ConP h _ ps) = do
  ps <- compilePats builtins ps
  c <- hsQName builtins (conName h)
  return $ pApp c ps
-- TODO: LitP
compilePat _ p = genericDocError =<< text "bad pattern:" <?> prettyTCM p

pApp :: Hs.QName () -> [Hs.Pat ()] -> Hs.Pat ()
pApp c@(Hs.UnQual () (Hs.Symbol () _)) [p, q] = Hs.PInfixApp () p c q
pApp c@(Hs.Special () Hs.Cons{}) [p, q] = Hs.PInfixApp () p c q
pApp c ps = Hs.PApp () c ps

eApp :: Hs.Exp () -> [Hs.Exp ()] -> Hs.Exp ()
eApp f (a : b : as) | Just op <- getOp f = foldl (Hs.App ()) (Hs.InfixApp () a op b) as
  where getOp (Hs.Var _ x) | isOp x = Just $ Hs.QVarOp () x
        getOp (Hs.Con _ c) | isOp c = Just $ Hs.QConOp () c
        getOp _                     = Nothing
eApp f es = foldl (Hs.App ()) f es

tApp :: Hs.Type () -> [Hs.Type ()] -> Hs.Type ()
tApp (Hs.TyCon () (Hs.Special () Hs.ListCon{})) [a] = Hs.TyList () a
tApp t vs = foldl (Hs.TyApp ()) t vs

hsLambda :: String -> Hs.Exp () -> Hs.Exp ()
hsLambda x e =
  case e of
    Hs.Lambda l ps b -> Hs.Lambda l (p : ps) b
    _                -> Hs.Lambda () [p] e
  where
    p = Hs.PVar () $ hsName x

-- FOREIGN pragmas --------------------------------------------------------

type Code = (Hs.Module Hs.SrcSpanInfo, [Hs.Comment])

getForeignPragmas :: TCM [(Range, Code)]
getForeignPragmas = do
  pragmas <- fromMaybe [] . Map.lookup pragmaName . iForeignCode <$> curIF
  reverse <$> mapM getCode pragmas
  where
    getCode :: ForeignCode -> TCM (Range, Code)
    getCode (ForeignCode r code) = do
          let Just file = fmap filePath $ toLazy $ rangeFile r
              pmode = Hs.defaultParseMode { Hs.parseFilename     = file,
                                            Hs.ignoreLinePragmas = False }
              line = case posLine <$> rStart r of
                       Just l  -> "{-# LINE " ++ show l ++ show file ++ " #-}\n"
                       Nothing -> ""
          case Hs.parseWithComments pmode (line ++ code) of
            Hs.ParseOk m           -> return (r, m)
            Hs.ParseFailed loc msg -> setCurrentRange (srcLocToRange loc) $ genericError msg

srcSpanToRange :: Hs.SrcSpan -> Range
srcSpanToRange (Hs.SrcSpan file l1 c1 l2 c2) =
  intervalToRange (toStrict $ Just $ mkAbsolute file) $ Interval (pos l1 c1) (pos l2 c2)
  where pos l c = Pn () 0 (fromIntegral l) (fromIntegral c)

srcLocToRange :: Hs.SrcLoc -> Range
srcLocToRange (Hs.SrcLoc file l c) = srcSpanToRange (Hs.SrcSpan file l c l c)

renderComment (Hs.Comment True  _ s) = "{-" ++ s ++ "-}"
renderComment (Hs.Comment False _ s) = "--" ++ s

-- Rendering --------------------------------------------------------------

type Block = (Range, [String])

sortRanges :: [(Range, a)] -> [a]
sortRanges = map snd . sortBy (compare `on` rLine . fst)

rLine :: Range -> Int
rLine r = fromIntegral $ fromMaybe 0 $ posLine <$> rStart r

renderBlocks :: [Block] -> String
renderBlocks = unlines . map unlines . sortRanges . filter (not . null . snd)

defBlock :: CompiledDef -> [Block]
defBlock def = [ (r, map pp ds) | (r, ds) <- def ]

codePragmas :: [(Range, Code)] -> [Block]
codePragmas code = [ (r, map pp ps) | (r, (Hs.Module _ _ ps _ _, _)) <- code ]

codeBlocks :: [(Range, Code)] -> [Block]
codeBlocks code = [(r, [uncurry Hs.exactPrint $ moveToTop $ noPragmas mcs]) | (r, mcs) <- code, nonempty mcs]
  where noPragmas (Hs.Module l h _ is ds, cs) = (Hs.Module l h [] is ds, cs)
        noPragmas m                           = m
        nonempty (Hs.Module _ _ _ is ds, cs) = not $ null is && null ds && null cs
        nonempty _                           = True

-- exactPrint really looks at the line numbers (and we're using the locations from the agda source
-- to report Haskell parse errors at the right location), so shift everything to start at line 1.
moveToTop :: Hs.Annotated ast => (ast Hs.SrcSpanInfo, [Hs.Comment]) -> (ast Hs.SrcSpanInfo, [Hs.Comment])
moveToTop (x, cs) = (subtractLine l <$> x, [ Hs.Comment b (sub l r) str | Hs.Comment b r str <- cs ])
  where l = Hs.startLine (Hs.ann x) - 1
        subtractLine :: Int -> Hs.SrcSpanInfo -> Hs.SrcSpanInfo
        subtractLine l (Hs.SrcSpanInfo s ss) = Hs.SrcSpanInfo (sub l s) (map (sub l) ss)

        sub :: Int -> Hs.SrcSpan -> Hs.SrcSpan
        sub l (Hs.SrcSpan f l0 c0 l1 c1) = Hs.SrcSpan f (l0 - l) c0 (l1 - l) c1

pp :: Hs.Pretty a => a -> String
pp = Hs.prettyPrintWithMode Hs.defaultMode{ Hs.spacing = False }

moduleFileName :: Options -> ModuleName -> FilePath
moduleFileName opts name =
  outDir opts </> C.moduleNameToFileName (toTopLevelModuleName name) "hs"

moduleSetup :: Options -> IsMain -> ModuleName -> FilePath -> TCM (Recompile ModuleEnv ModuleRes)
moduleSetup _ _ _ _ = do
  setScope . iInsideScope =<< curIF
  Recompile <$> getBuiltins

ensureDirectory :: FilePath -> IO ()
ensureDirectory = createDirectoryIfMissing True . takeDirectory

writeModule :: Options -> ModuleEnv -> IsMain -> ModuleName -> [CompiledDef] -> TCM ModuleRes
writeModule opts _ isMain m defs0 = do
  code <- getForeignPragmas
  let defs = concatMap defBlock defs0 ++ codeBlocks code
  unless (null code && null defs) $ do
    -- The comments makes it hard to generate and pretty print a full module
    let hsFile = moduleFileName opts m
        output = concat
                 [ renderBlocks $ codePragmas code
                 , "module " ++ prettyShow m ++ " where\n\n"
                 , renderBlocks defs ]
    reportSLn "" 1 $ "Writing " ++ hsFile
    liftIO $ ensureDirectory hsFile
    liftIO $ writeFile hsFile output

main = runAgda [Backend backend]

