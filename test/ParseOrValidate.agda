{-# OPTIONS --erasure #-}

open import Haskell.Prelude
open import Haskell.Control.Exception
open import Haskell.Control.Monad
open import Haskell.Extra.Dec
open import Haskell.Extra.Erase
open import Haskell.Extra.Refinement
open import Haskell.System.Environment

it : {{a}} → a
it {{x}} = x

{-# COMPILE AGDA2HS it inline #-}

{-# TERMINATING #-}
split : Char → String → List String
split c s = case rest of λ where
                []     → chunk ∷ []
                (_ ∷ rest) → chunk ∷ split c rest
  where
    broken = break (_== c) s
    chunk = fst broken
    rest = snd broken

{-# COMPILE AGDA2HS split #-}

-- The below example is taken from the classic blog post by Alexis King
-- "Parse, don't validate". Here I ignore her advice but instead implement
-- a validation function that returns evidence of the property it checked.

validateNonEmpty : @0 {{MayThrow IOException}} → (xs : List a) → IO (Erase (NonEmpty xs))
validateNonEmpty [] = throwIO (userError "list cannot be empty")
validateNonEmpty (x ∷ xs) = return it

{-# COMPILE AGDA2HS validateNonEmpty #-}

getConfigurationDirectories : @0 {{MayThrow IOException}} → IO (∃ (List FilePath) NonEmpty)
getConfigurationDirectories = do
  configDirsString <- getEnv "CONFIG_DIRS"
  let configDirsList = split ',' configDirsString
  validateNonEmpty configDirsList
  pure (configDirsList ⟨⟩)

{-# COMPILE AGDA2HS getConfigurationDirectories #-}

-- TODO: implement this function?
postulate
  initializeCache : String → IO ⊤
{-# COMPILE AGDA2HS initializeCache #-}

main : @0 {{MayThrow IOException}} → IO ⊤
main = do
  configDirs ⟨ i ⟩ <- getConfigurationDirectories
  initializeCache (head configDirs {{i}})

{-# COMPILE AGDA2HS main #-}
