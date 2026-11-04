-- | Pretty printing tweaks for @haskell-src-exts@.
module Agda2Hs.Language.Haskell.Pretty
  ( prettyShowImportDecl
  , prettyShowExportSpecList
  ) where

import Language.Haskell.Exts.Syntax as Hs

import Agda2Hs.Language.Haskell.Utils ( pp )

parenList :: [String] -> String
parenList [] = "()"
parenList (x:xs) = '(' : (x ++ go xs)
  where
    go :: [String] -> String
    go [] = ")"
    go (x:xs) = ", " ++ x ++ go xs

-- | Custom implementation of 'prettyShow' for 'Hs.ImportDecl'
-- that supports type operators.
--
-- Specifically, in the IThingAll and IThingWith import specs,
-- the "type" prefixes get before type operators if necessary.
-- See https://github.com/haskell-suite/haskell-src-exts/pull/475
-- If this pull request gets merged,
-- this custom implementation will be unnecessary.
prettyShowImportDecl :: Hs.ImportDecl () -> String
prettyShowImportDecl (Hs.ImportDecl _ m qual src safe mbPkg mbName mbSpecs) =
  unwords $ ("import" :) $
            (if src  then ("{-# SOURCE #-}" :) else id) $
            (if safe then ("safe" :) else id) $
            (if qual then ("qualified" :) else id) $
            maybeAppend (\ str -> show str) mbPkg $
            (pp m :) $
            maybeAppend (\m' -> "as " ++ pp m') mbName $
            (case mbSpecs of {Just specs -> [prettyShowSpecList specs]; Nothing -> []})
    where
      maybeAppend :: (a -> String) -> Maybe a -> ([String] -> [String])
      maybeAppend f (Just a) = (f a :)
      maybeAppend _ Nothing  = id

      prettyShowSpecList :: Hs.ImportSpecList () -> String
      prettyShowSpecList (Hs.ImportSpecList _ b ispecs)  =
            (if b then "hiding " else "")
                ++ parenList (map prettyShowSpec ispecs)

      -- this is why we have rewritten it
      prettyShowSpec :: Hs.ImportSpec () -> String
      prettyShowSpec (Hs.IVar _ name  )        = pp name
      prettyShowSpec (Hs.IAbs _ ns name)       = let ppns = pp ns in case ppns of
          []                                  -> pp name -- then we don't write a space before it
          _                                   -> ppns ++ (' ' : pp name)
      prettyShowSpec (Hs.IThingAll _ name) = let rest = pp name ++ "(..)" in
        case name of
          -- if it's a symbol, append a "type" prefix to the beginning
          (Hs.Symbol _ _)                     -> pp (Hs.TypeNamespace ()) ++ (' ' : rest)
          (Hs.Ident  _ _)                     -> rest
      prettyShowSpec (Hs.IThingWith _ name nameList) = let rest = pp name ++ (parenList . map pp $ nameList) in
        case name of
          (Hs.Symbol _ _)                     -> pp (Hs.TypeNamespace ()) ++ (' ' : rest)
          (Hs.Ident  _ _)                     -> rest

-- | Custom implementation of 'prettyShow' for 'Hs.ExportSpecList'
-- that supports type operators.
prettyShowExportSpecList :: Hs.ExportSpecList () -> String
prettyShowExportSpecList (Hs.ExportSpecList _ exps) =
  parenList $ map prettyShowSpec exps
  where
    prettyShowSpec :: Hs.ExportSpec () -> String
    prettyShowSpec spec@(Hs.EThingWith _ _ name _) =
      let rest = pp spec in
      case name of
        Hs.UnQual _ (Hs.Symbol {}) -> pp (Hs.TypeNamespace ()) ++ (' ' : rest)
        Hs.Qual _ _ (Hs.Symbol {}) -> pp (Hs.TypeNamespace ()) ++ (' ' : rest)
        _ -> rest
    prettyShowSpec spec = pp spec
