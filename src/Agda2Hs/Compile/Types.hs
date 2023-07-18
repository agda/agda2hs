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
import Agda2Hs.Compile.Rewrites

type ModuleEnv   = TopLevelModuleName
type ModuleRes   = ()
type CompiledDef = [Ranged [Hs.Decl ()]]
type Ranged a    = (Range, a)

type Code = (Hs.Module Hs.SrcSpanInfo, [Hs.Comment])

data Options = Options { optOutDir     :: Maybe FilePath,
                         optExtensions :: [Hs.Extension],
                         rewriteRules  :: Rewrites }
                      -- ^ the rewrite rules read from user-provided config files

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
