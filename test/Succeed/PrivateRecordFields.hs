module PrivateRecordFields
  (Secret(Secret), mkSecret, getSecret)
where

data Secret = Secret{hidden :: Int}

mkSecret :: Int -> Secret
mkSecret x = Secret x

getSecret :: Secret -> Int
getSecret (Secret x) = x

