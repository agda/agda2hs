{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}

module Agda2Hs.VersionCommitSuffix ( nameSuffix, versionSuffix ) where

#if defined(VERSION_WITH_GIT_HASH)
import Development.GitRev ( gitHash, gitDirtyTracked )
#endif

nameSuffix :: String
versionSuffix :: String

#if !defined(VERSION_WITH_GIT_HASH)
nameSuffix    = ""
versionSuffix = ""
#else
nameSuffix = "-dev"
versionSuffix
  | gitSHA == "UNKNOWN" = "-" ++ gitSHA
  | otherwise           = "-" ++ take 7 gitSHA ++ if codeModified then "-dirty" else ""
  where
    gitSHA       = $(gitHash)
    codeModified = $(gitDirtyTracked)
#endif
