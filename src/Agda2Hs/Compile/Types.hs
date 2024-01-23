{-# LANGUAGE PatternSynonyms, FlexibleInstances, MultiParamTypeClasses  #-}
module Agda2Hs.Compile.Types where

import Control.Applicative ( liftA2 )
import Control.Monad ( join )
import Control.Monad.Trans ( MonadTrans(lift) )
import Control.Monad.RWS ( RWST(..) )
import Control.Monad.RWS.Lazy ( runRWST )
import Control.Monad.State ( StateT(..) )
import Control.DeepSeq ( NFData(..) )

import Data.Maybe ( isJust )
import Data.Set ( Set )
import Data.Map ( Map )
import Data.String ( IsString(..) )

import qualified Language.Haskell.Exts.SrcLoc as Hs
import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Extension as Hs
import qualified Language.Haskell.Exts.Comments as Hs

import Agda.Compiler.Backend
import Agda.Syntax.Position ( Range )
import Agda.Syntax.TopLevelModuleName ( TopLevelModuleName )
import Agda.Utils.Null
import Agda.Utils.Impossible

import Agda2Hs.HsUtils ( Strictness )

type ModuleEnv   = TopLevelModuleName
type ModuleRes   = ()
type CompiledDef = [Ranged [Hs.Decl ()]]
type Ranged a    = (Range, a)

type Code = (Hs.Module Hs.SrcSpanInfo, [Hs.Comment])

-- | Custom substitution for a given definition.
data Rewrite = Rewrite
  { rewFrom   :: String
    -- ^ The fully qualified name.
  , rewTo     :: String
    -- ^ The corresponding Haskell name.
  , rewImport :: Maybe String
    -- ^ Haskell module to import.
  }

type Rewrites = [Rewrite]

-- | A lookup table for rewrite rules.
type SpecialRules = Map String (Hs.Name (), Maybe Import)

data PreludeOptions = PreludeOpts
  { preludeImplicit :: Bool
  , preludeImports  :: Maybe [String]
  , preludeHiding   :: [String]
  }
  -- ^ whether Prelude functions should be implicitly imported; if yes, then NamesToImport is a "hiding" list


data Options = Options
  { optIsEnabled  :: Bool
  , optOutDir     :: Maybe FilePath
  , optConfigFile :: Maybe FilePath
  , optExtensions :: [Hs.Extension]
  , optRewrites   :: SpecialRules
  , optPrelude    :: PreludeOptions
  }

-- Required by Agda-2.6.2, but we don't really care.
instance NFData Options where
  rnf _ = ()

-- | Names of local declarations (in @where@ blocks).
type LocalDecls = [QName]

data CompileEnv = CompileEnv
  { currModule :: TopLevelModuleName
  -- ^ the current module we are compiling
  , minRecordName :: Maybe ModuleName
  -- ^ keeps track of the current minimal record we are compiling
  , locals :: LocalDecls
  -- ^ keeps track of the current clause's where declarations
  , copatternsEnabled :: Bool
  -- ^ whether copatterns should be allowed when compiling patterns
  , checkVar :: Bool
  -- ^ whether to ensure compiled variables are usable and visible
  , rewrites :: SpecialRules
  -- ^ Special compilation rules.
  }

type Qualifier = Maybe (Maybe (Hs.ModuleName ()))

pattern Unqualified   = Nothing
pattern QualifiedAs m = Just m

isQualified :: Qualifier -> Bool
isQualified = isJust

qualifiedAs :: Qualifier -> Maybe (Hs.ModuleName ())
qualifiedAs = join

-- | Encoding of a Haskell module import statement.
data Import = Import
  { importModule    :: Hs.ModuleName ()
  , importQualified :: Qualifier
  , importParent    :: Maybe (Hs.Name ())
  , importName      :: Hs.Name ()
  , importNamespace :: Hs.Namespace ()
                    -- ^^ if this is a type or something like that, we can add a namespace qualifier to the import spec
                    -- now it's only useful for differentiating type operators; so for others we always put Hs.NoNamespace () here
                    -- (we don't calculate it if it's not necessary)
  }

type Imports = [Import]

-- | Output produced during the compilation of a module
data CompileOutput = CompileOutput
  { imports :: Imports
  -- ^ Haskell import statements.
  , haskellExtensions :: [Hs.KnownExtension]
  -- ^ Required language extensions.
  }

instance Semigroup CompileOutput where
  CompileOutput imps exts <> CompileOutput imps' exts' =
    CompileOutput (imps <> imps') (exts <> exts')

instance Monoid CompileOutput where
  mempty = CompileOutput mempty mempty

-- | State used while compiling a single module.
newtype CompileState = CompileState
  { lcaseUsed :: Int
    -- ^ How many @\case@ have been generated in the output Haskell code.
    --   Can be removed by subsequent program transformations, hence the StateT.
  }

-- TODO: see if we should use RWS.CPS
-- | Compilation monad.
type C = RWST CompileEnv CompileOutput CompileState TCM

-- some missing instances from the Agda side
instance HasFresh i => MonadFresh i C
instance MonadTCState C
instance MonadTCEnv C
instance HasOptions C
instance ReadTCState C
instance MonadTCM C
instance MonadTrace C where
  traceClosureCall c f = RWST $ \ r s -> traceClosureCall c $ runRWST f r s
instance MonadInteractionPoints C where
instance MonadDebug C where
instance HasConstInfo C where
instance MonadReduce C where
instance MonadAddContext C where
instance HasBuiltins C where
instance MonadBlock C where
  catchPatternErr h m = RWST $ \ r s ->
    let run x = runRWST x r s in catchPatternErr (run . h) (run m)
instance MonadStConcreteNames C where
  runStConcreteNames m = RWST $ \r s -> runStConcreteNames $ StateT $ \ns -> do
    ((x, ns'), s', w) <- runRWST (runStateT m ns) r s
    pure ((x, s', w), ns')
instance IsString a => IsString (C a) where fromString = pure . fromString
instance PureTCM C where
instance Null a => Null (C a) where
  empty = lift empty
  null = __IMPOSSIBLE__
instance Semigroup a => Semigroup (C a) where (<>) = liftA2 (<>)


-- | Currently we can compile an Agda "Dom Type" in three ways:
-- To a type in Haskell (with perhaps a strictness annotation)
-- To a typeclass constraint in Haskell
-- To nothing (e.g. for proofs)
data CompiledDom
  = DomType Strictness (Hs.Type ())
  | DomConstraint (Hs.Asst ())
  | DomDropped

-- | Whether a datatype/record should be compiled as a @newtype@ haskell definition.
type AsNewType = Bool

-- | Compilation target for an Agda record definition.
data RecordTarget
  = ToRecord AsNewType [Hs.Deriving ()]
  | ToClass [String]

-- | Compilation target for an Agda instance declaration.
data InstanceTarget
  = ToDefinition
  | ToDerivation (Maybe (Hs.DerivStrategy ()))

-- Used when compiling imports. If there is a type operator, we can append a "type" namespace here.
data NamespacedName = NamespacedName
  { nnNamespace :: Hs.Namespace ()
  , nnName      :: Hs.Name ()
  } deriving (Eq, Ord)
