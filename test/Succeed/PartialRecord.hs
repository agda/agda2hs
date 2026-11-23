module PartialRecord
  (PartiallyExported(PartiallyExported), exportedField)
where

data PartiallyExported = PartiallyExported{exportedField :: Int,
                                           hiddenField :: Int}

