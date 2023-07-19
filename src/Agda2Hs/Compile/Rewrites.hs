-- Reads custom rewrite rules of the user from a YAML config file.
module Agda2Hs.Compile.Rewrites where

import Data.Yaml.YamlLight
import qualified Data.Map as Map
import qualified Data.Text as Text
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import qualified Data.ByteString as ByteString

-- There is already a RewriteRule identifier in Agda internals, hence the name.
-- Elements:
  -- the identifier to rewrite ("from")
  -- the identifier with which we replace it ("to")
  -- the import to use, if any ("importing")
data Rewrite = Rewrite {from :: String, to :: String, importing :: Maybe String}

type Rewrites = [Rewrite]

-- Read rewrite rules from a given file. Fail if the format is incorrect (necessary fields are absent).
readRewritesFromFile :: FilePath -> IO Rewrites
readRewritesFromFile fname = rulesFromYaml <$> parseYamlFile fname

-- Read rewrite rules from a YamlLight object. Fail if the format is incorrect.
rulesFromYaml :: YamlLight -> Rewrites
rulesFromYaml y = case y of
  YNil -> []
  YSeq ls -> map ruleFromElement ls
  otherYaml -> error $ "Incorrect format for the rewrite rules file: must be a list of elements – " ++ show otherYaml
  where
    -- parsing a single element
    ruleFromElement :: YamlLight -> Rewrite
    ruleFromElement (YMap dmap) = case (safeRuleFromMap dmap) of
      Right rule -> rule
      Left e     -> error e
    ruleFromElement otherYaml   = error $ "Not a map: " ++ show otherYaml
    
    safeRuleFromMap :: Map.Map YamlLight YamlLight -> Either String Rewrite
    safeRuleFromMap yamlMap = do
      let dmap = Map.mapKeys unpackString $ Map.map unpackString yamlMap
      from <- safeLookup (pure "from") dmap
      to   <- safeLookup (pure "to") dmap
      case Map.lookup (Right "importing") dmap of
        Just (Right lib) -> Right $ Rewrite from to (Just lib)
        Just (Left e)    -> Left e
        Nothing          -> Right $ Rewrite from to Nothing

    -- not too pretty... but Map.Map is not Traversable
    safeLookup :: Either String String -> Map.Map (Either String String) (Either String String) -> Either String String
    safeLookup key dmap = case Map.lookup key dmap of
      Just val -> val
      Nothing  -> Left $ "Key not found: " ++ show key

    unpackString :: YamlLight -> Either String String
    unpackString yaml = case (unStr yaml) of
      Just bytestr -> Right $ byteStringToString $ bytestr
      Nothing      -> Left $ "Not a string element: " ++ show yaml

-- Conversions from String to ByteString and vice versa.
-- We assume UTF-8.
stringToByteString :: String -> ByteString.ByteString
stringToByteString = encodeUtf8 . Text.pack
byteStringToString :: ByteString.ByteString -> String
byteStringToString = Text.unpack . decodeUtf8
