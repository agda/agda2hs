module ParseOrValidate where

import Control.Exception (throwIO)
import System.Environment (getEnv)

split :: Char -> String -> [String]
split c s
  = case rest of
        [] -> [chunk]
        _ : rest -> chunk : split c rest
  where
    broken :: ([Char], [Char])
    broken = break (== c) s
    chunk :: [Char]
    chunk = fst broken
    rest :: [Char]
    rest = snd broken

validateNonEmpty :: [a] -> IO ()
validateNonEmpty [] = throwIO (userError "list cannot be empty")
validateNonEmpty (x : xs) = return ()

getConfigurationDirectories :: IO [FilePath]
getConfigurationDirectories
  = do configDirsString <- getEnv "CONFIG_DIRS"
       validateNonEmpty (split ',' configDirsString)
       pure (split ',' configDirsString)

initializeCache :: String -> IO ()
initializeCache = error "postulate: String -> IO ()"

main :: IO ()
main
  = do configDirs <- getConfigurationDirectories
       initializeCache (head configDirs)

