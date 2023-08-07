module Haskell.Prim.IO where

open import Haskell.Prim
open import Haskell.Prim.Show
open import Haskell.Prim.String

postulate IO : ∀{a} → Set a → Set a

FilePath = String

postulate
  -- Input functions
  interact       : (String → String) → IO ⊤
  getContents    : IO String
  getLine        : IO String
  getChar        : IO Char

  -- Output functions
  print          : ⦃ Show a ⦄ → a → IO ⊤
  putChar        : Char → IO ⊤
  putStr         : String → IO ⊤
  putStrLn       : String → IO ⊤

  -- Files
  readFile       : FilePath → IO String
  writeFile      : FilePath → String → IO ⊤
  appendFile     : FilePath → String → IO ⊤
