
open import Haskell.Prelude
open import Haskell.Control.Exception

module Haskell.System.Environment where

postulate
  getArgs : IO (List String)
  getProgName : IO String
  executablePath : Maybe (IO (Maybe FilePath))
  getExecutablePath : IO FilePath
  getEnv : @0 {{MayThrow IOException}} → String → IO String
  lookupEnv : String → IO (Maybe String)
  setEnv : @0 {{MayThrow IOException}} → String → String → IO ⊤
  unsetEnv : @0 {{MayThrow IOException}} → String → IO ⊤
  withArgs : List String → IO a → IO a
  withProgName : String → IO a → IO a
  getEnvironment : IO (List (String × String))
