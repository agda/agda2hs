module Haskell.System.Environment where

open import Haskell.Prelude
open import Haskell.Control.Exception

postulate
  getArgs : IO (List String)
  getProgName : IO String
  executablePath : Maybe (IO (Maybe FilePath))
  getExecutablePath : IO FilePath
  getEnv : String → IO String
  lookupEnv : String → IO (Maybe String)
  setEnv : String → String → IO ⊤
  unsetEnv : String → IO ⊤
  withArgs : List String → IO a → IO a
  withProgName : String → IO a → IO a
  getEnvironment : IO (List (String × String))
{-# COMPILE AGDA2HS getArgs existing #-}
{-# COMPILE AGDA2HS getProgName existing #-}
{-# COMPILE AGDA2HS executablePath existing #-}
{-# COMPILE AGDA2HS getExecutablePath existing #-}
{-# COMPILE AGDA2HS getEnv existing #-}
{-# COMPILE AGDA2HS lookupEnv existing #-}
{-# COMPILE AGDA2HS setEnv existing #-}
{-# COMPILE AGDA2HS unsetEnv existing #-}
{-# COMPILE AGDA2HS withArgs existing #-}
{-# COMPILE AGDA2HS withProgName existing #-}
{-# COMPILE AGDA2HS getEnvironment existing #-}
