-- Reads custom rewrite rules of the user from a YAML config file.
module Agda2Hs.Compile.Rewrites (readConfigFile) where

import Data.Yaml.YamlLight
import qualified Data.Map as Map
import qualified Data.Text as Text
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import qualified Data.ByteString as ByteString
import Data.Char (toLower)
import Data.Maybe (isJust)

import Agda2Hs.Compile.Types

-- Conversions from String to ByteString and vice versa.
-- We assume UTF-8.
stringToByteString :: String -> ByteString.ByteString
stringToByteString = encodeUtf8 . Text.pack
byteStringToString :: ByteString.ByteString -> String
byteStringToString = Text.unpack . decodeUtf8

-- A simple element consisting of the string given. Useful when looking up maps.
stringElement :: String -> YamlLight
stringElement = YStr . stringToByteString

-- Read Prelude options from a YamlLight object. Fail if the format is incorrect.
preludeOptionsFromYaml :: YamlLight -> Maybe PreludeOptions
preludeOptionsFromYaml yaml = case lookupYL (stringElement "prelude") yaml of
  Nothing            -> Nothing
  Just (YMap dmap)   -> Just $ preludeOptionsFromMap dmap
  Just otherYaml     -> error $ "Incorrect format for the rewrite rules file: the \"prelude\" element must be a map – " ++ show otherYaml
  where
    preludeOptionsFromMap :: Map.Map YamlLight YamlLight -> PreludeOptions
    preludeOptionsFromMap dmap = (impl, namesToImp)
      where
        impl :: Bool
        impl = case Map.lookup (stringElement "implicit") dmap of
          Nothing        -> isJust $ Map.lookup (YStr $ stringToByteString "hiding") dmap
          Just (YStr bs) -> let str = map toLower $ byteStringToString bs in
                             str == "true" || str == "yes"
          Just otherYaml -> error "Incorrect format for the rewrite rules file: \"implicit\" must be a boolean"

        namesToImp :: NamesToImport
        namesToImp = if impl then hidingNames else importingNames         -- we search for different keys
          where
            hidingNames :: NamesToImport
            hidingNames = case Map.lookup (stringElement "hiding") dmap of
              Nothing        -> Names []    -- then we import the whole Prelude
              Just (YSeq ls) -> Names $ map (parseElement "hiding") $ ls
              Just otherYaml -> error "Incorrect format for the rewrite rules file: \"hiding\" must be a sequence"

            importingNames :: NamesToImport
            importingNames = case Map.lookup (stringElement "using") dmap of
              Nothing        -> Auto       -- then we let agda2hs search for them
              Just (YSeq ls) -> Names $ map (parseElement "using") $ ls
              Just otherYaml -> error "Incorrect format for the rewrite rules file: \"\" must be a sequence"

            parseElement :: String -> YamlLight -> String
            parseElement seqName y = case (unStr y) of
              Nothing -> error "Incorrect format for the rewrite rules file: an element in \"" ++ seqName ++ "\" was not a string"
              Just bs -> byteStringToString bs

-- Read rewrite rules from a YamlLight object. Fail if the format is incorrect.
rulesFromYaml :: YamlLight -> Rewrites
rulesFromYaml y = case lookupYL (stringElement "rules") y of
  Nothing           -> case y of   -- maybe the root is the sequence
                         YSeq ls -> map ruleFromElement ls
                         _       -> []
  Just YNil         -> []
  Just (YSeq ls)    -> map ruleFromElement ls
  Just otherYaml    -> error $ "Incorrect format for the rewrite rules file: \"rules\" must be a list of elements – " ++ show otherYaml
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

-- The exported function to be used in Main.hs.
readConfigFile :: FilePath -> IO Config
readConfigFile fname = (,) <$>
                       (preludeOptionsFromYaml <$> wholeYaml) <*>
                       (rulesFromYaml <$> wholeYaml)
  where
    wholeYaml :: IO YamlLight
    wholeYaml = parseYamlFile fname
