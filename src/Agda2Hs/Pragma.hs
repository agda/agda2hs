module Agda2Hs.Pragma where

import Data.List ( isPrefixOf )
import Data.Maybe ( fromMaybe )
import qualified Data.Map as Map
import qualified Data.Text as Text

import Agda.Compiler.Backend
import Agda.Compiler.Common ( curIF )

import Agda.Syntax.Position
import Agda.TypeChecking.Pretty (text)

import Agda.Utils.FileName ( filePath )
import Agda.Utils.Maybe.Strict ( toLazy )

import Agda2Hs.Compile.Types

import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils ( Strictness(..), srcLocToRange )

pragmaName :: Text.Text
pragmaName = "AGDA2HS"

languagePragmas :: Code -> [Hs.Extension]
languagePragmas (Hs.Module _ _ ps _ _, _) =
  [ Hs.parseExtension s | Hs.LanguagePragma _ ss <- ps, Hs.Ident _ s <- ss ]
languagePragmas _ = []

getForeignPragmas :: [Hs.Extension] -> TCM [(Range, Code)]
getForeignPragmas exts = do
  pragmas <- fromMaybe [] . fmap getForeignCodeStack . Map.lookup pragmaName . iForeignCode <$> curIF
  getCode exts $ reverse pragmas
  where
    getCode :: [Hs.Extension] -> [ForeignCode] -> TCM [(Range, Code)]
    getCode _ [] = return []
    getCode exts (ForeignCode r code : pragmas) = do
          let Just file = fmap (filePath . rangeFilePath) $ toLazy $ rangeFile r
              pmode = Hs.defaultParseMode { Hs.parseFilename     = file,
                                            Hs.ignoreLinePragmas = False,
                                            Hs.extensions        = exts }
              line = case posLine <$> rStart r of
                       Just l  -> "{-# LINE " ++ show l ++ show file ++ " #-}\n"
                       Nothing -> ""
          case Hs.parseWithComments pmode (line ++ code) of
            Hs.ParseFailed loc msg -> setCurrentRange (srcLocToRange loc) $ typeError <$> CustomBackendError "agda2hs" =<< text msg
            Hs.ParseOk m           -> ((r, m) :) <$> getCode (exts ++ languagePragmas m) pragmas

data ParsedPragma
  = NoPragma
  | InlinePragma
  | DefaultPragma [Hs.Deriving ()]
  | ClassPragma [String]
  | ExistingClassPragma
  | UnboxPragma Strictness
  | TransparentPragma
  | NewTypePragma [Hs.Deriving ()]
  | TuplePragma Hs.Boxed
  | DerivePragma (Maybe (Hs.DerivStrategy ()))
  deriving (Eq, Show)

derivePragma :: String
derivePragma = "derive"

parseStrategy :: String -> Maybe (Hs.DerivStrategy ())
parseStrategy "stock"    = Just (Hs.DerivStock ())
parseStrategy "newtype"  = Just (Hs.DerivNewtype ())
parseStrategy "anyclass" = Just (Hs.DerivAnyclass ())
parseStrategy _          = Nothing

newtypePragma :: String
newtypePragma = "newtype"

processDeriving :: Range -> String -> ([Hs.Deriving ()] -> ParsedPragma) -> C ParsedPragma
processDeriving r d pragma = do
  -- parse a deriving clause for a datatype by tacking it onto a
  -- dummy datatype and then only keeping the deriving part
  case Hs.parseDecl ("data X = X " ++ d) of
    Hs.ParseFailed loc msg -> do
      setCurrentRange r $ typeError <$> CustomBackendError "agda2hs" =<< text msg
    Hs.ParseOk (Hs.DataDecl _ _ _ _ _ ds) ->
      return $ pragma (map (() <$) ds)
    Hs.ParseOk _ -> return $ pragma []

processPragma :: QName -> C ParsedPragma
processPragma qn = liftTCM (getUniqueCompilerPragma pragmaName qn) >>= \case
  Nothing -> return NoPragma
  Just (CompilerPragma r s)
    | "class" `isPrefixOf` s      -> return $ ClassPragma (words $ drop 5 s)
    | s == "inline"               -> return InlinePragma
    | s == "existing-class"       -> return ExistingClassPragma
    | s == "unboxed"              -> return $ UnboxPragma Lazy
    | s == "unboxed-strict"       -> return $ UnboxPragma Strict
    | s == "transparent"          -> return TransparentPragma
    | s == "tuple"                -> return $ TuplePragma Hs.Boxed
    | s == "unboxed-tuple"        -> return $ TuplePragma Hs.Unboxed
    | s == newtypePragma          -> return $ NewTypePragma []
    | s == derivePragma           -> return $ DerivePragma Nothing
    | derivePragma `isPrefixOf` s -> return $ DerivePragma (parseStrategy (drop (length derivePragma + 1) s))
    | "deriving"   `isPrefixOf` s -> processDeriving r s DefaultPragma
    | (newtypePragma ++ " deriving") `isPrefixOf` s -> processDeriving r (drop (length newtypePragma + 1) s) NewTypePragma
  _ -> return $ DefaultPragma []
