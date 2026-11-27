module ExistingPattern
  (mkAF, getAF)
where

import Control.Exception (AssertionFailed(AssertionFailed))

mkAF :: String -> AssertionFailed
mkAF s = AssertionFailed s

getAF :: AssertionFailed -> String
getAF (AssertionFailed s) = s

