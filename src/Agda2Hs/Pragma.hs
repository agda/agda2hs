module Agda2Hs.Pragma where

import Data.List ( isPrefixOf )
import Data.Maybe
import qualified Data.Map as Map

import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Parser as Hs
import qualified Language.Haskell.Exts.Extension as Hs

import Agda.Compiler.Backend
import Agda.Compiler.Common

import Agda.Syntax.Position

import Agda.Utils.FileName
import Agda.Utils.Maybe.Strict ( toLazy )

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

data ParsedPragma
  = NoPragma
  | DefaultPragma
  | ClassPragma [String]
  | ExistingClassPragma
  | DerivingPragma [Hs.Deriving ()]
  deriving Show

processPragma :: QName -> C ParsedPragma
processPragma qn = liftTCM (getUniqueCompilerPragma pragmaName qn) >>= \case
  Nothing -> return NoPragma
  Just (CompilerPragma _ s)
    | "class" `isPrefixOf` s    -> return $ ClassPragma (words $ drop 5 s)
    | s == "existing-class"     -> return ExistingClassPragma
    | "deriving" `isPrefixOf` s ->
      -- parse a deriving clause for a datatype by tacking it onto a
      -- dummy datatype and then only keeping the deriving part
      case Hs.parseDecl ("data X = X " ++ s) of
        Hs.ParseFailed loc msg ->
          setCurrentRange (srcLocToRange loc) $ genericError msg
        Hs.ParseOk (Hs.DataDecl _ _ _ _ _ ds) ->
          return $ DerivingPragma (map (() <$) ds)
        Hs.ParseOk _ -> return DefaultPragma
  _ -> return DefaultPragma
