module Issue185 where

newtype RecordTest = MkRecord{aBool :: Bool}

aBoolAsAFunction :: RecordTest -> Bool
aBoolAsAFunction r = aBool r

test :: Bool
test = aBoolAsAFunction (MkRecord True)

