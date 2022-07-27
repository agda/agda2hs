module Agda2Hs.Compile.Types where

import Control.Monad.Reader
import Control.DeepSeq
import qualified Language.Haskell.Exts.SrcLoc as Hs
import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Extension as Hs
import qualified Language.Haskell.Exts.Comments as Hs

import Agda.Compiler.Backend
import Agda.Syntax.Position

type ModuleEnv   = ModuleName
type ModuleRes   = ()
type CompiledDef = [Ranged [Hs.Decl ()]]
type Ranged a    = (Range, a)

type Code = (Hs.Module Hs.SrcSpanInfo, [Hs.Comment])

data Options = Options { optOutDir     :: FilePath,
                         optExtensions :: [Hs.Extension] }

-- Required by Agda-2.6.2, but we don't really care.
instance NFData Options where
  rnf _ = ()

data CompileEnv = CompileEnv
  { minRecordName :: Maybe ModuleName
  }

type C = ReaderT CompileEnv TCM

-- Currently we can compile an Agda "Dom Type" in three ways:
-- - To a type in Haskell
-- - To a typeclass constraint in Haskell
-- - To nothing (e.g. for proofs)
data CompiledDom
  = DomType (Hs.Type ())
  | DomConstraint (Hs.Asst ())
  | DomDropped

type LocalDecls = [(QName, Definition)]

data RecordTarget = ToRecord | ToClass [String]
