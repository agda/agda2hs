module CompileToGadt
  (toRes)
where

import CompileToGadtTarget (Res(MkRes))

toRes :: a -> Res a
toRes = MkRes

