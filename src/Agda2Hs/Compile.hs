module Agda2Hs.Compile where

import Control.Monad.Trans.RWS.CPS ( evalRWST )
import Control.Monad.State ( gets )
import Control.Arrow ((>>>))
import Data.Functor

import qualified Data.Map as M

import Agda.Compiler.Backend
import Agda.Syntax.TopLevelModuleName ( TopLevelModuleName )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Monad.Signature ( isInlineFun )
import Agda.Utils.Null
import Agda.Utils.Monad ( whenM )

import qualified Language.Haskell.Exts.Extension as Hs

import Agda2Hs.Compile.ClassInstance ( compileInstance )
import Agda2Hs.Compile.Data ( compileData )
import Agda2Hs.Compile.Function ( compileFun, checkTransparentPragma, checkInlinePragma )
import Agda2Hs.Compile.Postulate ( compilePostulate )
import Agda2Hs.Compile.Record ( compileRecord, checkUnboxPragma )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils ( setCurrentRangeQ, tellExtension )
import Agda2Hs.Pragma

initCompileEnv :: TopLevelModuleName -> SpecialRules -> CompileEnv
initCompileEnv tlm rewrites = CompileEnv
  { currModule        = tlm
  , minRecordName     = Nothing
  , locals            = []
  , copatternsEnabled = False
  , checkVar          = False
  , rewrites          = rewrites
  }

initCompileState :: CompileState
initCompileState = CompileState { lcaseUsed = 0 }

runC :: TopLevelModuleName -> SpecialRules -> C a -> TCM (a, CompileOutput)
runC tlm rewrites c = evalRWST c (initCompileEnv tlm rewrites) initCompileState

-- Main compile function
------------------------

compile
  :: Options -> ModuleEnv -> IsMain -> Definition 
  -> TCM (CompiledDef, CompileOutput)
compile opts tlm _ def =
  withCurrentModule (qnameModule qname)
    $ runC tlm (optRewrites opts)
    $ setCurrentRangeQ qname
    $ compileAndTag <* postCompile
  where
    qname = defName def
    tag code = [(nameBindingSite $ qnameName qname, code)]

    compileAndTag :: C CompiledDef
    compileAndTag = tag <$> do
      p <- processPragma qname

      reportSDoc "agda2hs.compile" 5  $ text "Compiling definition:" <+> prettyTCM qname
      reportSDoc "agda2hs.compile" 45 $ text "Pragma:" <+> text (show p)
      reportSDoc "agda2hs.compile" 45 $ text "Compiling definition:" <+> pretty (theDef def)

      case (p , defInstance def , theDef def) of
        (NoPragma            , _      , _         ) -> return []
        (ExistingClassPragma , _      , _         ) -> return []
        (UnboxPragma s       , _      , defn      ) -> [] <$ checkUnboxPragma defn
        (TransparentPragma   , _      , Function{}) -> [] <$ checkTransparentPragma def
        (InlinePragma        , _      , Function{}) -> [] <$ checkInlinePragma def

        (ClassPragma ms      , _      , Record{}  ) -> pure <$> compileRecord (ToClass ms) def
        (NewTypePragma ds    , _      , Record{}  ) -> pure <$> compileRecord (ToRecord True ds) def
        (NewTypePragma ds    , _      , Datatype{}) -> compileData True ds def
        (DefaultPragma ds    , _      , Datatype{}) -> compileData False ds def
        (DerivePragma s      , Just _ , _         ) -> pure <$> compileInstance (ToDerivation s) def
        (DefaultPragma _     , Just _ , Axiom{}   ) -> pure <$> compileInstance (ToDerivation Nothing) def
        (DefaultPragma _     , Just _ , _         ) -> pure <$> compileInstance ToDefinition def
        (DefaultPragma _     , _      , Axiom{}   ) -> compilePostulate def
        (DefaultPragma _     , _      , Function{}) -> compileFun True def
        (DefaultPragma ds    , _      , Record{}  ) -> pure <$> compileRecord (ToRecord False ds) def

        _ -> genericDocError =<<  text "Don't know how to compile" <+> prettyTCM (defName def)

    postCompile :: C ()
    postCompile = whenM (gets $ lcaseUsed >>> (> 0)) $ tellExtension Hs.LambdaCase
