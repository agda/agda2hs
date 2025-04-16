```haskell
module IOInput where

main :: IO ()
main
  = do putStrLn "Write something "
       x <- getLine
       putStr $ "You wrote: " ++ x
       return ()

```
