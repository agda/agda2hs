-- | Querying the names exported by the Haskell @Prelude@, so that we can
-- check that user-defined symbols do not clash with them.
--
-- The names are obtained from the user's @ghc@ by browsing the @Prelude@
-- module. This means the check is always in sync with the Haskell compiler
-- that will eventually compile the generated code. If @ghc@ cannot be
-- found or the output cannot be parsed, 'queryPreludeNames' returns
-- 'Nothing' and the clash check is skipped with a warning.
module Agda2Hs.PreludeNames
  ( PreludeNames(..)
  , queryPreludeNames
  , parsePreludeBrowse
  ) where

import Control.Exception ( SomeException, try )
import Data.Char ( isAlphaNum, isSpace, isUpper )
import Data.List ( isPrefixOf, isInfixOf )
import Data.Set ( Set )
import qualified Data.Set as Set

import System.Exit ( ExitCode(..) )
import System.Process ( readProcessWithExitCode )

-- | The names exported by the Haskell @Prelude@, split by namespace.
-- Haskell keeps separate namespaces for values, data constructors, and
-- type constructors/classes, so we keep them separate as well to avoid
-- false positives (e.g. a constructor named @Bool@ does not clash with
-- the type @Bool@).
data PreludeNames = PreludeNames
  { preludeVals :: Set String
    -- ^ Value-level names: functions and class methods.
  , preludeCons :: Set String
    -- ^ Data constructor names.
  , preludeTys  :: Set String
    -- ^ Type constructor and class names.
  }

-- | Run @ghc -e ':browse Prelude'@ and parse the result. Returns 'Nothing'
-- if @ghc@ is not available or the command fails.
queryPreludeNames :: IO (Maybe PreludeNames)
queryPreludeNames = do
  result <- try (readProcessWithExitCode "ghc"
                   ["-v0", "-ignore-dot-ghci", "-e", ":browse Prelude"] "")
    :: IO (Either SomeException (ExitCode, String, String))
  pure $ case result of
    Right (ExitSuccess, out, _) | not (null out) -> Just (parsePreludeBrowse out)
    _                                            -> Nothing

-- | Parse the output of @:browse Prelude@.
parsePreludeBrowse :: String -> PreludeNames
parsePreludeBrowse = foldl addEntry emptyPreludeNames
                   . groupEntries
                   . filter (not . null)
                   . lines
  where
    emptyPreludeNames = PreludeNames Set.empty Set.empty Set.empty

    addEntry :: PreludeNames -> [String] -> PreludeNames
    addEntry pn [] = pn
    addEntry pn entry@(l : ls)
      | "type"    `isPrefixOf` l = addTy  (nameAfter "type" l) pn
      | "data"    `isPrefixOf` l = addData pn entry
      | "newtype" `isPrefixOf` l = addData pn entry
      | "class"   `isPrefixOf` l = addClass pn entry
      | "pattern" `isPrefixOf` l = addCon (nameAfter "pattern" l) pn
      | "::" `isInfixOf` l       = maybe pn (`addVal` pn) (nameBefore "::" l)
      | otherwise                = pn

    addData :: PreludeNames -> [String] -> PreludeNames
    addData pn entry =
      let decl = unwords entry
          kw   = if "newtype" `isPrefixOf` decl then "newtype" else "data"
          pn'  = addTy (nameAfter kw decl) pn
          rhs  = drop 1 $ dropWhile (/= '=') decl
          cons = [ normalizeName (takeWhile (not . isSpace) (dropWhile isSpace c))
                 | c <- splitOn '|' rhs
                 , not (null (dropWhile isSpace c))
                 ]
      in foldr addCon pn' cons

    addClass :: PreludeNames -> [String] -> PreludeNames
    addClass pn [] = pn
    addClass pn (l : ls) =
      let pn' = addTy (normalizeName (classHead l)) pn
          methods = [ n | l' <- ls
                        , not ("{-#" `isPrefixOf` dropWhile isSpace l')
                        , Just n <- [nameBefore "::" l']
                        ]
      in foldr addVal pn' methods

    -- The head of a class declaration is the part after the context (if any).
    classHead :: String -> String
    classHead l =
      let afterCtx = case lastBreak "=>" l of
            Just rest -> rest
            Nothing   -> drop (length ("class" :: String)) l
      in takeWhile (not . isSpace) (dropWhile isSpace afterCtx)

    -- Extract the first token following the given keyword at the start of a line.
    nameAfter :: String -> String -> String
    nameAfter kw l = normalizeName $ takeWhile (not . isSpace) $ dropWhile isSpace $ drop (length kw) l

    -- Extract the token before the given separator.
    nameBefore :: String -> String -> Maybe String
    nameBefore sep l = case splitOnStr sep l of
      Just (name, _) | not (null (dropWhile isSpace name)) -> Just (normalizeName name)
      _ -> Nothing

    addTy :: String -> PreludeNames -> PreludeNames
    addTy n pn | null n    = pn
               | otherwise = pn { preludeTys = Set.insert n (preludeTys pn) }

    addCon :: String -> PreludeNames -> PreludeNames
    addCon n pn | null n    = pn
                | otherwise = pn { preludeCons = Set.insert n (preludeCons pn) }

    addVal :: String -> PreludeNames -> PreludeNames
    addVal n pn | null n    = pn
                | otherwise = pn { preludeVals = Set.insert n (preludeVals pn) }

-- | Group the output into top-level entries, where an entry is a
-- non-indented line followed by all the indented lines that belong to it.
groupEntries :: [String] -> [[String]]
groupEntries [] = []
groupEntries (l : ls)
  | isIndented l = groupEntries ls
  | otherwise    = let (cont, rest) = span isIndented ls
                   in (l : cont) : groupEntries rest

isIndented :: String -> Bool
isIndented l = case l of
  (c : _) -> isSpace c
  _       -> False

-- | Remove module qualification and outer parentheses from a name.
normalizeName :: String -> String
normalizeName = stripParens . stripModule . trim
  where
    trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse
    stripParens ('(' : s) | not (null s), lastMay s == Just ')' = reverse (drop 1 (reverse s))
    stripParens s = s
    stripModule s = case span isModuleChar s of
      (m@(_ : _), '.' : rest) | isUpper (first m) -> stripModule rest
      _ -> s
    isModuleChar c = isAlphaNum c || c == '_' || c == '\''

first :: String -> Char
first (c : _) = c
first []      = error "Agda2Hs.PreludeNames.first: empty string"

lastMay :: String -> Maybe Char
lastMay s = case reverse s of
  (c : _) -> Just c
  []      -> Nothing

-- | Split a string on a delimiter character.
splitOn :: Char -> String -> [String]
splitOn c s = case break (== c) s of
  (x, [])       -> [x]
  (x, _ : rest) -> x : splitOn c rest

-- | Split a string at the first occurrence of a delimiter string, returning
-- the part before and after it.
splitOnStr :: String -> String -> Maybe (String, String)
splitOnStr needle hay = go "" hay
  where
    go acc s
      | needle `isPrefixOf` s = Just (reverse acc, drop (length needle) s)
      | otherwise             = case s of
          []       -> Nothing
          (c : cs) -> go (c : acc) cs

-- | Split a string at the last occurrence of a delimiter, returning the part
-- after the delimiter.
lastBreak :: String -> String -> Maybe String
lastBreak needle hay = go Nothing hay
  where
    go acc s
      | needle `isPrefixOf` s = go (Just (drop (length needle) s)) (drop 1 s)
      | otherwise             = case s of
          []       -> acc
          (_ : cs) -> go acc cs
