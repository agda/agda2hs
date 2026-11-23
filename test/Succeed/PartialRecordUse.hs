module PartialRecordUse
  (getExported)
where

import PartialRecord (PartiallyExported(exportedField))

getExported :: PartiallyExported -> Int
getExported = \ r -> exportedField r

