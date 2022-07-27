module Agda2Hs.Compile.Data where

import Control.Arrow ( (>>>), (***), (&&&), first, second )
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader

import Data.Generics ( mkT, everywhere, listify, extT, everything, mkQ, Data )
import Data.List
import Data.List.NonEmpty ( NonEmpty(..) )
import Data.Maybe
import Data.Map ( Map )
import qualified Data.Text as Text
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap

import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Build as Hs
import qualified Language.Haskell.Exts.Parser as Hs
import qualified Language.Haskell.Exts.Extension as Hs

import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.BasicOps

import Agda.Syntax.Common hiding ( Ranged )
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad hiding ( withCurrentModule )

import Agda.TypeChecking.CheckInternal ( infer )
import Agda.TypeChecking.Constraints ( noConstraints )
import Agda.TypeChecking.Conversion ( equalTerm )
import Agda.TypeChecking.InstanceArguments ( findInstance )
import Agda.TypeChecking.Level ( isLevelType )
import Agda.TypeChecking.MetaVars ( newInstanceMeta )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce ( instantiate, reduce )
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Records
import Agda.TypeChecking.Sort ( ifIsSort )

import Agda.Utils.Lens
import Agda.Utils.Pretty ( prettyShow )
import qualified Agda.Utils.Pretty as P
import Agda.Utils.List
import Agda.Utils.Impossible
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Functor

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.ClassInstance
import Agda2Hs.Compile.Function
import Agda2Hs.Compile.Name
import Agda2Hs.Compile.Type
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.HsUtils
import Agda2Hs.Pragma

compileData :: [Hs.Deriving ()] -> Definition -> C [Hs.Decl ()]
compileData ds def = do
  let d = hsName $ prettyShow $ qnameName $ defName def
  case theDef def of
    Datatype{dataPars = n, dataIxs = numIxs, dataCons = cs} -> do
      TelV tel t <- telViewUpTo n (defType def)
      reportSDoc "agda2hs.data" 10 $ text "Datatype telescope:" <+> prettyTCM tel
      allIndicesErased t
      params <- compileTele tel
      addContext tel $ do
        pars <- mapM (showTCM . unArg) params
        cs   <- mapM (compileConstructor params) cs
        let hd   = foldl (\ h p -> Hs.DHApp () h (Hs.UnkindedVar () $ hsName p))
                         (Hs.DHead () d) pars
        return [Hs.DataDecl () (Hs.DataType ()) Nothing hd cs ds]
    _ -> __IMPOSSIBLE__
  where
    allIndicesErased :: Type -> C ()
    allIndicesErased t = reduce (unEl t) >>= \case
      Pi dom t -> compileDom (absName t) dom >>= \case
        DomDropped      -> allIndicesErased (unAbs t)
        DomType{}       -> genericDocError =<< text "Not supported: indexed datatypes"
        DomConstraint{} -> genericDocError =<< text "Not supported: constraints in types"
      _ -> return ()

compileConstructor :: [Arg Term] -> QName -> C (Hs.QualConDecl ())
compileConstructor params c = do
  ty <- (`piApplyM` params) . defType =<< getConstInfo c
  TelV tel _ <- telView ty
  let conName = hsName $ prettyShow $ qnameName c
  args <- compileConstructorArgs tel
  return $ Hs.QualConDecl () Nothing Nothing $ Hs.ConDecl () conName args

compileConstructorArgs :: Telescope -> C [Hs.Type ()]
compileConstructorArgs EmptyTel = return []
compileConstructorArgs (ExtendTel a tel) = compileDom (absName tel) a >>= \case
  DomType hsA       -> (hsA :) <$> underAbstraction a tel compileConstructorArgs
  DomConstraint hsA -> genericDocError =<< text "Not supported: constructors with class constraints"
  DomDropped        -> underAbstraction a tel compileConstructorArgs
