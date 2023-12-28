-- This is to ensure
-- we can import compileType
-- in Compile.Term.
module Agda2Hs.Compile.Type where
    import qualified Language.Haskell.Exts as Hs
    import Agda.Syntax.Internal ( Term )
    import Agda2Hs.Compile.Types

    compileType :: Term -> C (Hs.Type ())

