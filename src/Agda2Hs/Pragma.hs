module Agda2Hs.Pragma where


import Control.Applicative
import Control.Arrow ((>>>), (***), (&&&), first, second)
import Control.Monad
import Control.Monad.Except
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

import Agda2Hs.HsUtils
import Agda2Hs.Compile.Types

pragmaName :: String
pragmaName = "AGDA2HS"

languagePragmas :: Code -> [Hs.Extension]
languagePragmas (Hs.Module _ _ ps _ _, _) =
  [ Hs.parseExtension s | Hs.LanguagePragma _ ss <- ps, Hs.Ident _ s <- ss ]
languagePragmas _ = []

getForeignPragmas :: [Hs.Extension] -> TCM [(Range, Code)]
getForeignPragmas exts = do
  pragmas <- fromMaybe [] . Map.lookup pragmaName . iForeignCode <$> curIF
  getCode exts $ reverse pragmas
  where
    getCode :: [Hs.Extension] -> [ForeignCode] -> TCM [(Range, Code)]
    getCode _ [] = return []
    getCode exts (ForeignCode r code : pragmas) = do
          let Just file = fmap filePath $ toLazy $ rangeFile r
              pmode = Hs.defaultParseMode { Hs.parseFilename     = file,
                                            Hs.ignoreLinePragmas = False,
                                            Hs.extensions        = exts }
              line = case posLine <$> rStart r of
                       Just l  -> "{-# LINE " ++ show l ++ show file ++ " #-}\n"
                       Nothing -> ""
          case Hs.parseWithComments pmode (line ++ code) of
            Hs.ParseFailed loc msg -> setCurrentRange (srcLocToRange loc) $ genericError msg
            Hs.ParseOk m           -> ((r, m) :) <$> getCode (exts ++ languagePragmas m) pragmas
