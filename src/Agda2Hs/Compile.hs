module Agda2Hs.Compile where

import Control.Monad.Reader ( ReaderT(runReaderT) )
import Control.Monad.Writer ( WriterT(runWriterT) )
import Control.Monad.State ( StateT, evalStateT, get )

import qualified Data.Map as M

import Agda.Compiler.Backend
import Agda.Syntax.TopLevelModuleName ( TopLevelModuleName )
import Agda.TypeChecking.Pretty
import Agda.Utils.Null
import Agda.Utils.Monad ( whenM )

import qualified Language.Haskell.Exts.Extension as Hs

import Agda2Hs.Compile.ClassInstance ( compileInstance )
import Agda2Hs.Compile.Data ( compileData )
import Agda2Hs.Compile.Function ( compileFun, checkTransparentPragma )
import Agda2Hs.Compile.Postulate ( compilePostulate )
import Agda2Hs.Compile.Record ( compileRecord, checkUnboxPragma )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils ( setCurrentRangeQ, tellExtension )
import Agda2Hs.Pragma

-- Needs a list of rewrite rules too.
initCompileEnv :: TopLevelModuleName -> SpecialRules -> CompileEnv
initCompileEnv tlm rewrites = CompileEnv
  { currModule = tlm
  , minRecordName = Nothing
  , locals = []
  , copatternsEnabled = False
  , checkVar = False
  , rewrites = rewrites
  }

initCompileState :: CompileState
initCompileState = CompileState { lcaseUsed = 0 }

runC :: TopLevelModuleName -> SpecialRules -> C a -> TCM (a, CompileOutput)
runC tlm rewrites = runWriterT
     . flip runReaderT (initCompileEnv tlm rewrites)
     . flip evalStateT initCompileState

-- Main compile function
------------------------

compile :: Options -> ModuleEnv -> IsMain -> Definition ->
  TCM (CompiledDef, CompileOutput)
compile opts tlm _ def = withCurrentModule (qnameModule $ defName def) $ runC tlm (optRewrites opts) $
  compileAndTag <* postCompile
  where
    tag code = [(nameBindingSite $ qnameName $ defName def, code)]
    single x = [x]

    compileAndTag :: C CompiledDef
    compileAndTag = processPragma (defName def) >>= \ p -> 
      setCurrentRangeQ (defName def) $ do
        reportSDoc "agda2hs.compile" 5 $
          text "Compiling definition: " <+> prettyTCM (defName def)
        reportSDoc "agda2hs.compile" 45 $
          text "Pragma: " <+> text (show p)
        reportSDoc "agda2hs.compile" 45 $
          text "Compiling definition: " <+> pretty (theDef def)
        case (p , defInstance def , theDef def) of
          (NoPragma, _, _) ->
            return []
          (ExistingClassPragma, _, _) ->
            return [] -- No code generation, but affects how projections are compiled
          (UnboxPragma s, _, defn) ->
            checkUnboxPragma defn >> return [] -- also no code generation
          (TransparentPragma  , _, Function{}) ->
            checkTransparentPragma def >> return [] -- also no code generation
          (ClassPragma ms, _, Record{}) ->
            tag . single <$> compileRecord (ToClass ms) def
          (NewTypePragma ds, _, Record{}) ->
            tag . single <$> compileRecord (ToRecordNewType ds) def
          (NewTypePragma ds, _, Datatype{}) ->
            tag <$> compileData ToDataNewType ds def
          (DefaultPragma ds, _, Datatype{}) ->
            tag <$> compileData ToData ds def
          (DerivePragma s, Just _, _) ->
            tag . single <$> compileInstance (ToDerivation s) def
          (DefaultPragma _, Just _, Axiom{}) ->
            tag . single <$> compileInstance (ToDerivation Nothing) def
          (DefaultPragma _, Just _, _) ->
            tag . single <$> compileInstance ToDefinition def
          (DefaultPragma _, _, Axiom{}) ->
            tag <$> compilePostulate def
          (DefaultPragma _, _, Function{}) ->
            tag <$> compileFun True def
          (DefaultPragma ds, _, Record{}) ->
            tag . single <$> compileRecord (ToRecord ds) def
          _ ->
            genericDocError =<< do
            text "Don't know how to compile" <+> prettyTCM (defName def)

    postCompile :: C ()
    postCompile =
      whenM ((> 0) . lcaseUsed <$> get) $
        tellExtension Hs.LambdaCase
