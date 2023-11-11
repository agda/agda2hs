{-# LANGUAGE OverloadedStrings #-}
-- Read additional configuration options from a file.
module Agda2Hs.Config (checkConfig) where

import Control.Monad.IO.Class ( MonadIO )
import GHC.Generics

import Data.Functor ( (<&>) )
import Data.Maybe ( fromMaybe )
import Data.Aeson ( FromJSON(parseJSON), withObject, (.:) )
import qualified Data.Map.Strict as Map
import qualified Data.Yaml as Yaml ( decodeFileThrow )

import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Name ( toNameImport )
import Agda.TypeChecking.Monad.Base (TCM)

-- | Config file data.
data Config = Config
  { cfgPrelude  :: Maybe PreludeOptions
  , cfgRewrites :: Rewrites
  }

instance FromJSON Rewrite where
  parseJSON = withObject "rewrite rule" $ \v ->
    Rewrite <$> v .: "from"
            <*> v .: "to"
            <*> v .: "importing"

instance FromJSON PreludeOptions where
  parseJSON = withObject "prelude options" $ \v ->
    PreludeOpts <$> v .: "implicit"
                <*> v .: "using"
                <*> v .: "hiding"

instance FromJSON Config where
  parseJSON = withObject "config" $ \v ->
    Config <$> v .: "prelude"
           <*> v .: "rewrites"

readConfigFile :: MonadIO m => FilePath -> m Config
readConfigFile = Yaml.decodeFileThrow

applyConfig :: Options -> Config -> Options
applyConfig opts cfg =
  opts { optPrelude  = fromMaybe (optPrelude opts) (cfgPrelude cfg)
       , optRewrites = foldl addRewrite (optRewrites opts) (cfgRewrites cfg)
       }
  where addRewrite :: SpecialRules -> Rewrite -> SpecialRules
        addRewrite rules (Rewrite from to importing) = Map.insert from (toNameImport to importing) rules

checkConfig :: Options -> TCM Options
checkConfig opts
  | Just src <- optConfigFile opts
  = readConfigFile src <&> applyConfig opts
checkConfig opts = return opts

