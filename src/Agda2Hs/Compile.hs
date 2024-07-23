module Agda2Hs.Compile where

import Control.Monad.Trans.RWS.CPS ( evalRWST )
import Control.Monad.State ( gets )
import Control.Arrow ((>>>))
import Data.Functor
import Data.List ( isPrefixOf, group, sort )

import qualified Data.Map as M

import Agda.Compiler.Backend
import Agda.Compiler.Common ( curIF )
import Agda.Syntax.TopLevelModuleName ( TopLevelModuleName )
import Agda.Syntax.Common.Pretty ( prettyShow )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Monad.Signature ( isInlineFun )
import Agda.Utils.Null
import Agda.Utils.Monad ( whenM, anyM, when )

import qualified Language.Haskell.Exts.Extension as Hs

import Agda2Hs.Compile.ClassInstance ( compileInstance )
import Agda2Hs.Compile.Data ( compileData )
import Agda2Hs.Compile.Function ( compileFun, checkTransparentPragma, checkInlinePragma )
import Agda2Hs.Compile.Postulate ( compilePostulate )
import Agda2Hs.Compile.Record ( compileRecord, checkUnboxPragma )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils ( setCurrentRangeQ, tellExtension, primModules, isClassName )
import Agda2Hs.Pragma
import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Pretty as Hs


initCompileEnv :: TopLevelModuleName -> SpecialRules -> CompileEnv
initCompileEnv tlm rewrites = CompileEnv
  { currModule        = tlm
  , minRecordName     = Nothing
  , locals            = []
  , compilingLocal    = False
  , copatternsEnabled = False
  , rewrites          = rewrites
  }

initCompileState :: CompileState
initCompileState = CompileState { lcaseUsed = 0 }

runC :: TopLevelModuleName -> SpecialRules -> C a -> TCM (a, CompileOutput)
runC tlm rewrites c = evalRWST c (initCompileEnv tlm rewrites) initCompileState

moduleSetup :: Options -> IsMain -> TopLevelModuleName -> Maybe FilePath -> TCM (Recompile ModuleEnv ModuleRes)
moduleSetup _ _ m _ = do
  -- we never compile primitive modules
  if any (`isPrefixOf` prettyShow m) primModules then pure $ Skip ()
  else do
    reportSDoc "agda2hs.compile" 3 $ text "Compiling module: " <+> prettyTCM m
    setScope . iInsideScope =<< curIF
    return $ Recompile m

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

    tag []   = []
    tag code = [(nameBindingSite $ qnameName qname, code)]

    compileAndTag :: C CompiledDef
    compileAndTag = tag <$> do
      p <- processPragma qname

      reportSDoc "agda2hs.compile" 5  $ text "Compiling definition:" <+> prettyTCM qname
      reportSDoc "agda2hs.compile" 45 $ text "Pragma:" <+> text (show p)
      reportSDoc "agda2hs.compile" 45 $ text "Compiling definition:" <+> pretty (theDef def)

      isInstance <- anyM (defInstance def) isClassName

      reportSDoc "agda2hs.compile" 15  $ text "Is instance?" <+> prettyTCM isInstance

      case (p , theDef def) of
        (NoPragma            , _         ) -> return []
        (ExistingClassPragma , _         ) -> return []
        (UnboxPragma s       , Record{}  ) -> [] <$ checkUnboxPragma def
        (TransparentPragma   , Function{}) -> [] <$ checkTransparentPragma def
        (InlinePragma        , Function{}) -> [] <$ checkInlinePragma def
        (TuplePragma b       , Record{}  ) -> return []

        (ClassPragma ms      , Record{}  ) -> pure <$> compileRecord (ToClass ms) def
        (NewTypePragma ds    , Record{}  ) -> pure <$> compileRecord (ToRecord True ds) def
        (NewTypePragma ds    , Datatype{}) -> compileData True ds def
        (DefaultPragma ds    , Datatype{}) -> compileData False ds def
        (DerivePragma s      , _         ) | isInstance -> pure <$> compileInstance (ToDerivation s) def
        (DefaultPragma _     , Axiom{}   ) | isInstance -> pure <$> compileInstance (ToDerivation Nothing) def
        (DefaultPragma _     , _         ) | isInstance -> pure <$> compileInstance ToDefinition def
        (DefaultPragma _     , Axiom{}   ) -> compilePostulate def
        (DefaultPragma _     , Function{}) -> compileFun True def
        (DefaultPragma ds    , Record{}  ) -> pure <$> compileRecord (ToRecord False ds) def

        _ -> genericDocError =<<  text "Don't know how to compile" <+> prettyTCM (defName def)

    postCompile :: C ()
    postCompile = whenM (gets $ lcaseUsed >>> (> 0)) $ tellExtension Hs.LambdaCase

verifyOutput ::
  Options -> ModuleEnv -> IsMain -> TopLevelModuleName
  -> [(CompiledDef, CompileOutput)] -> TCM Bool
verifyOutput _ _ _ m ls = do
  reportSDoc "agda2hs.compile" 5 $ text "Checking generated output before rendering: " <+> prettyTCM m
  ensureUniqueConstructors
  where
    ensureUniqueConstructors = do
      let allCons = do
            (r, _) <- ls
            (_, a) <- r
            Hs.DataDecl _ _ _ _ cons _ <- a
            Hs.QualConDecl _ _ _ con <- cons
            return $ case con of
              Hs.ConDecl _ n _ -> n
              Hs.InfixConDecl _ _ n _ -> n
              Hs.RecDecl _ n _ -> n
          duplicateCons = filter ((> 1) . length) . group . sort  $ allCons
      when (length duplicateCons > 0) $
        genericDocError =<< vcat (map (\x -> text $ "Cannot generate multiple constructors with the same identifier: " <> Hs.prettyPrint (head x)) duplicateCons)
      return (length duplicateCons == 0)
