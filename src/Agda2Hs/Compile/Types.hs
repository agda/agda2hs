{-# LANGUAGE PatternSynonyms #-}
module Agda2Hs.Compile.Types where

import Control.Monad.Reader ( ReaderT )
import Control.Monad.Writer ( WriterT )
import Control.Monad.State ( StateT )
import Control.DeepSeq ( NFData(..) )

import Data.Maybe ( fromMaybe, isJust )
import Data.Set ( Set )
import Data.Map ( Map )

import qualified Language.Haskell.Exts.SrcLoc as Hs
import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Extension as Hs
import qualified Language.Haskell.Exts.Comments as Hs

import Agda.Compiler.Backend ( Definition, QName, ModuleName, TCM )
import Agda.Syntax.Position ( Range )
import Agda.Syntax.TopLevelModuleName ( TopLevelModuleName )

import Agda2Hs.HsUtils ( Strictness )

type ModuleEnv   = TopLevelModuleName
type ModuleRes   = ()
type CompiledDef = [Ranged [Hs.Decl ()]]
type Ranged a    = (Range, a)

type Code = (Hs.Module Hs.SrcSpanInfo, [Hs.Comment])

-- For config files and rewrite rules.
-- There is already a RewriteRule identifier in Agda internals, hence the name.
-- Elements:
  -- the identifier to rewrite ("from")
  -- the identifier with which we replace it ("to")
  -- the import to use, if any ("importing")
data Rewrite = Rewrite {from :: String, to :: String, importing :: Maybe String}

type Rewrites = [Rewrite]

data NamesToImport = Auto | Names [String]     -- Auto if Prelude is explicit and we want agda2hs to figure out the import list by itself

type PreludeOptions = (Bool, NamesToImport)
                       -- ^ whether Prelude functions should be implicitly imported; if yes, then NamesToImport is a "hiding" list

-- The type of an entire parsed config file.
type Config = (Maybe PreludeOptions, Rewrites)
            -- ^ Nothing if there was no "prelude" element in the file

data Options = Options { optIsEnabled         :: Bool,
                      -- ^ false if the backend is disabled because we want vanilla Agda behaviour (important for Emacs)
                         optOutDir            :: Maybe FilePath,
                         optExtensions        :: [Hs.Extension],
                         optRewrites          :: Rewrites,
                      -- ^ the rewrite rules read from user-provided config files
                         optPrelude           :: PreludeOptions }
                      -- ^ options on how to handle Prelude; see Agda2Hs.Compile.Rewrites

-- Required by Agda-2.6.2, but we don't really care.
instance NFData Options where
  rnf _ = ()

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
  , rewrites :: Rewrites
  -- ^ the user-defined rewrite rules read from a config file
  }

type Qualifier = Maybe (Maybe (Hs.ModuleName ()))
pattern Unqualified   = Nothing
pattern QualifiedAs m = Just m

isQualified = isJust
qualifiedAs = fromMaybe Nothing

data CompilingCategory = ClassInstance | CaseOf | MonadicBind
  deriving Eq

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

data CompileOutput = CompileOutput
  { imports :: Imports
  -- ^ Information we generate during compilation related to import statements.
  , haskellExtensions :: [Hs.KnownExtension]
  -- ^ Necessary language extensions to be automatically inserted.
  }

instance Semigroup CompileOutput where
  CompileOutput imps exts <> CompileOutput imps' exts' =
    CompileOutput (imps ++ imps') (exts ++ exts')

instance Monoid CompileOutput where
  mempty = CompileOutput [] []

-- | State used while compiling a single module.
data CompileState = CompileState
  { lcaseUsed :: Int
  -- ^ Keeps track of how many times we've used an extension.
  -- NB: can be removed by subsequent program transformations, hence the StateT.
  }

type C = StateT CompileState (ReaderT CompileEnv (WriterT CompileOutput TCM))

-- Currently we can compile an Agda "Dom Type" in three ways:
-- - To a type in Haskell (with perhaps a strictness annotation)
-- - To a typeclass constraint in Haskell
-- - To nothing (e.g. for proofs)
data CompiledDom
  = DomType Strictness (Hs.Type ())
  | DomConstraint (Hs.Asst ())
  | DomDropped

type LocalDecls = [QName]

data DataTarget = ToData | ToDataNewType

data RecordTarget = ToRecord [Hs.Deriving ()] | ToRecordNewType [Hs.Deriving ()] | ToClass [String]

data InstanceTarget = ToDefinition | ToDerivation (Maybe (Hs.DerivStrategy ()))

-- Used when compiling imports. If there is a type operator, we can append a "type" namespace here.
data NamespacedName = NamespacedName { nnNamespace :: Hs.Namespace (),
                                       nnName      :: Hs.Name ()
                                     }
                      deriving (Eq, Ord)
