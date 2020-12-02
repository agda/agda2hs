module HsUtils where

import Data.Data
import Data.Generics.Schemes (listify)

import Language.Haskell.Exts.SrcLoc
import Language.Haskell.Exts.Syntax
import Language.Haskell.Exts.Build
import Language.Haskell.Exts.Comments
import Language.Haskell.Exts.Pretty

import Agda.Syntax.Position
import Agda.Utils.FileName
import Agda.Utils.List
import Agda.Utils.Maybe.Strict (toStrict)

-- Names ------------------------------------------------------------------

isInfix :: String -> Maybe String
isInfix ('_' : f) = do
  (op, '_') <- initLast f
  return op
isInfix _ = Nothing

hsName :: String -> Name ()
hsName x
  | Just op <- isInfix x = Symbol () op
  | otherwise            = Ident () (map underscore x)
  where
    -- Agda uses underscores for operators, which means that you can't have both mapM and mapM_
    -- without getting ambiguities. To work around this we translate subscript '-' to underscore.
    underscore '₋' = '_'
    underscore c   = c

isOp :: QName () -> Bool
isOp (UnQual _ Symbol{}) = True
isOp (Special _ Cons{})  = True
isOp _                   = False

-- Utilities for building Haskell constructs

pp :: Pretty a => a -> String
pp = prettyPrintWithMode defaultMode{ spacing = False }

-- exactPrint really looks at the line numbers (and we're using the locations from the agda source
-- to report Haskell parse errors at the right location), so shift everything to start at line 1.
moveToTop :: Annotated ast => (ast SrcSpanInfo, [Comment]) -> (ast SrcSpanInfo, [Comment])
moveToTop (x, cs) = (subtractLine l <$> x, [ Comment b (sub l r) str | Comment b r str <- cs ])
  where l = startLine (ann x) - 1
        subtractLine :: Int -> SrcSpanInfo -> SrcSpanInfo
        subtractLine l (SrcSpanInfo s ss) = SrcSpanInfo (sub l s) (map (sub l) ss)

        sub :: Int -> SrcSpan -> SrcSpan
        sub l (SrcSpan f l0 c0 l1 c1) = SrcSpan f (l0 - l) c0 (l1 - l) c1

pApp :: QName () -> [Pat ()] -> Pat ()
pApp c@(UnQual () (Symbol () _)) [p, q] = PInfixApp () p c q
pApp c@(Special () Cons{}) [p, q] = PInfixApp () p c q
pApp c ps = PApp () c ps

getOp :: Exp () -> Maybe (QOp ())
getOp (Var _ x) | isOp x = Just $ QVarOp () x
getOp (Con _ c) | isOp c = Just $ QConOp () c
getOp _                  = Nothing

eApp :: Exp () -> [Exp ()] -> Exp ()
eApp f (a : b : as) | Just op <- getOp f = foldl (App ()) (InfixApp () a op b) as
eApp f [a]          | Just op <- getOp f = LeftSection () a op
eApp f es = foldl (App ()) f es

tApp :: Type () -> [Type ()] -> Type ()
tApp (TyCon () (Special () ListCon{})) [a] = TyList () a
tApp t vs = foldl (TyApp ()) t vs

hsLambda :: String -> Exp () -> Exp ()
hsLambda x e =
  case e of
    Lambda l ps b -> Lambda l (p : ps) b
    _             -> Lambda () [p] e
  where
    p = PVar () $ hsName x

hsUndefined :: Exp ()
hsUndefined = Var () $ UnQual () (hsName "undefined")

hsError :: String -> Exp ()
hsError s = Var () (UnQual () $ hsName "error") `eApp` [strE s]

getExplicitImports :: ImportSpec l -> [String]
getExplicitImports = map pp . \case
  IVar _ n -> [n]
  IAbs _ _ n -> [n]
  IThingAll _ n -> [n]
  IThingWith _ n ns -> n : map cname ns

cname :: CName l -> Name l
cname (VarName _ n) = n
cname (ConName _ n) = n

cloc :: CName l -> l
cloc (VarName l _) = l
cloc (ConName l _) = l

srcSpanToRange :: SrcSpan -> Range
srcSpanToRange (SrcSpan file l1 c1 l2 c2) =
  intervalToRange (toStrict $ Just $ mkAbsolute file) $ Interval (pos l1 c1) (pos l2 c2)
  where pos l c = Pn () 0 (fromIntegral l) (fromIntegral c)

srcLocToRange :: SrcLoc -> Range
srcLocToRange (SrcLoc file l c) = srcSpanToRange (SrcSpan file l c l c)

srcSpanInfoToRange :: SrcSpanInfo -> Range
srcSpanInfoToRange = srcSpanToRange . srcInfoSpan

allUsedTypes :: Data a => a -> [Type ()]
allUsedTypes = listify (const True)

usedTypesOf :: Data a => String -> a -> [Type ()]
usedTypesOf s = listify $ (== s) . pp

usesWord64 :: Data a => a -> Bool
usesWord64 = not . null . usedTypesOf "Word64"
