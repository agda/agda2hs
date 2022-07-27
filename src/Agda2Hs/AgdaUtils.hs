module Agda2Hs.AgdaUtils where

import Control.Applicative
import Control.Arrow ((>>>), (***), (&&&), first, second)
import Control.Monad
import Control.Monad.Error
import Control.Monad.Fail (MonadFail)
import Control.Monad.Reader
import Control.Monad.IO.Class
import Control.DeepSeq
import Data.Data
import Data.Generics (mkT, everywhere, listify, extT, everything, mkQ, Data)
import Data.Function
import Data.List
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as List1
import Data.Maybe
import Data.Map (Map)
import qualified Data.Text as Text
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap
import Data.Set (Set)
import qualified Data.Set as Set
import System.Console.GetOpt
import System.Environment
import System.FilePath
import System.Directory

import qualified Language.Haskell.Exts.SrcLoc     as Hs
import qualified Language.Haskell.Exts.Syntax     as Hs
import qualified Language.Haskell.Exts.Build      as Hs
import qualified Language.Haskell.Exts.Pretty     as Hs
import qualified Language.Haskell.Exts.Parser     as Hs
import qualified Language.Haskell.Exts.ExactPrint as Hs
import qualified Language.Haskell.Exts.Extension  as Hs
import qualified Language.Haskell.Exts.Comments   as Hs

import Agda.Main (runAgda)
import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.BasicOps
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty hiding (pretty)
import Agda.Syntax.Common hiding (Ranged)
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Translation.ConcreteToAbstract hiding (topLevelModuleName)
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad hiding (withCurrentModule)
import Agda.TheTypeChecker
import Agda.TypeChecking.CheckInternal (infer)
import Agda.TypeChecking.Constraints (noConstraints)
import Agda.TypeChecking.Conversion (equalTerm)
import Agda.TypeChecking.Free
import Agda.TypeChecking.InstanceArguments (findInstance)
import Agda.TypeChecking.Level (isLevelType)
import Agda.TypeChecking.MetaVars (newInstanceMeta)
import Agda.TypeChecking.Rules.Term (isType_)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Records
import Agda.TypeChecking.Sort
import Agda.Utils.Lens
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.FileName
import Agda.Utils.List
import Agda.Utils.Impossible
import Agda.Utils.Maybe.Strict (toLazy, toStrict)
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.Functor

multilineText :: Monad m => String -> m Doc
multilineText s = vcat $ map text $ lines s

(~~) :: QName -> String -> Bool
q ~~ s = prettyShow q == s

applyNoBodies :: Definition -> [Arg Term] -> Definition
applyNoBodies d args = revert $ d `apply` args
  where
    bodies :: [Maybe Term]
    bodies = map clauseBody $ funClauses $ theDef d

    setBody cl b = cl { clauseBody = b }

    revert :: Definition -> Definition
    revert d@(Defn {theDef = f@(Function {funClauses = cls})}) =
      d {theDef = f {funClauses = zipWith setBody cls bodies}}
    revert _ = __IMPOSSIBLE__

-- | Convert the final 'Proj' projection elimination into a
--   'Def' projection application.
unSpine1 :: Term -> Term
unSpine1 v =
  case hasElims v of
    Just (h, es) -> fromMaybe v $ loop h [] es
    Nothing      -> v
  where
    loop :: (Elims -> Term) -> Elims -> Elims -> Maybe Term
    loop h res es =
      case es of
        []             -> Nothing
        Proj o f : es' -> Just $ fromMaybe (Def f (Apply (defaultArg v) : es')) $ loop h (Proj o f : res) es'
        e        : es' -> loop h (e : res) es'
      where v = h $ reverse res
