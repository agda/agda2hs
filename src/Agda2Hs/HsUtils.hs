
module Agda2Hs.HsUtils where

import Control.Monad ( guard )

import Data.Data ( Data )
import Data.Generics ( listify, everywhere, mkT, extT )
import Data.List ( foldl' )
import Data.Map ( Map )

import qualified Data.Map as Map

import Language.Haskell.Exts hiding ( Strict, Lazy )

import Agda.Syntax.Position

import Agda.Utils.FileName ( mkAbsolute )
import Agda.Utils.List ( initLast )
import Agda.Utils.Maybe.Strict ( toStrict )

-- Names ------------------------------------------------------------------


validVarId :: String -> Bool
validVarId s = case lexTokenStream s of
  ParseOk [Loc _ VarId{}] -> True
  _ -> False

validConId :: String -> Bool
validConId s = case lexTokenStream s of
  ParseOk [Loc _ ConId{}] -> True
  _ -> False

validVarSym :: String -> Bool
validVarSym s = case lexTokenStream s of
  ParseOk [Loc _ VarSym{}] -> True
  _ -> False

validConSym :: String -> Bool
validConSym s = case lexTokenStream s of
  ParseOk [Loc _ ConSym{}] -> True
  _ -> False

validVarName :: Name () -> Bool
validVarName (Ident _ s)  = validVarId s
validVarName (Symbol _ s) = validVarSym s

validTypeName :: Name () -> Bool
validTypeName (Ident _ s) = validConId s
validTypeName (Symbol _ s) = validVarSym s || validConSym s -- type operators need not start with a colon

validConName :: Name () -> Bool
validConName (Ident _ s)  = validConId s
validConName (Symbol _ s) = validConSym s

isInfix :: String -> Maybe String
isInfix ('_' : f) = do
  (op, '_') <- initLast f
  guard $ not $ '_' `elem` op
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

extToName :: KnownExtension -> Name ()
extToName = Ident () . show

hsModuleName :: String -> ModuleName ()
hsModuleName = ModuleName ()

isOp :: QName () -> Bool
isOp (UnQual _ Symbol{}) = True
isOp (Special _ Cons{})  = True
isOp _                   = False

isSpecial :: QName () -> Bool
isSpecial (Special _ _)  = True
isSpecial _              = False

unQual :: QName () -> Name ()
unQual (UnQual _ n) = n
unQual (Qual _ _ n) = n
unQual (Special _ _)  = error "Unexpected special con"

definedName :: Match l -> Name l
definedName (Match _ f _ _ _) = f
definedName (InfixMatch _ _ f _ _ _) = f

replaceName :: Data a => Name () -> Name () -> a -> a
replaceName pre post = everywhere (mkT go `extT` go')
  where
    go :: QName () -> QName ()
    go n | isSpecial n = n
         | unQual n == pre = UnQual () post
         | otherwise = n

    go' :: Match () -> Match ()
    go' m = case m of
      (Match () n ps rhs bs) -> Match () (f n) ps rhs bs
      (InfixMatch () p n ps rhs bs) -> InfixMatch () p (f n) ps rhs bs
      where f n | n == pre  = post
                | otherwise = n

dropPatterns :: Data a => Int -> a -> a
dropPatterns n = everywhere (mkT go)
  where
    go :: Match () -> Match ()
    go (Match () f ps rhs bs) = Match () f (drop n ps) rhs bs
    go m = m


-- Utilities for building Haskell constructs

pp :: Pretty a => a -> String
pp = prettyPrintWithMode defaultMode{ spacing = False
                                    , classIndent = 4
                                    , whereIndent = 2
                                    }


-- exactPrint really looks at the line numbers (and we're using the locations from the agda source
-- to report Haskell parse errors at the right location), so shift everything to start at line 1.
moveToTop :: Annotated ast => (ast SrcSpanInfo, [Comment]) -> (ast SrcSpanInfo, [Comment])
moveToTop (x, cs) = (subtractLine l <$> x, [ Comment b (sub l r) str | Comment b r str <- cs ])
  where l = startLine (ann x) - 1
        subtractLine :: Int -> SrcSpanInfo -> SrcSpanInfo
        subtractLine l (SrcSpanInfo s ss) = SrcSpanInfo (sub l s) (map (sub l) ss)

        sub :: Int -> SrcSpan -> SrcSpan
        sub l (SrcSpan f l0 c0 l1 c1) = SrcSpan f (l0 - l) c0 (l1 - l) c1

getList :: Exp () -> Maybe [Exp ()]
getList (Con _ (Special _ ListCon{})) = Just []
getList (List _ es)                   = Just es
getList _                             = Nothing

getListP :: Pat () -> Maybe [Pat ()]
getListP (PApp _ (Special _ ListCon{}) []) = Just []
getListP (PList _ es)                      = Just es
getListP _                                 = Nothing

pApp :: QName () -> [Pat ()] -> Pat ()
pApp c@(UnQual () (Symbol () _)) [p, q]                = PInfixApp () p c q
pApp (Special _ Cons{}) [p, q] | Just ps <- getListP q = PList () (p : ps)
pApp c@(Special () Cons{}) [p, q]                      = PInfixApp () p c q
pApp c ps                                              = PApp () c ps

getOp :: Exp () -> Maybe (QOp ())
getOp (Var _ x) | isOp x = Just $ QVarOp () x
getOp (Con _ c) | isOp c = Just $ QConOp () c
getOp _                  = Nothing

eApp :: Exp () -> [Exp ()] -> Exp ()
eApp f [a, b] | Just (QConOp () (Special _ Cons{})) <- getOp f,
                Just as <- getList b = List () (a : as)
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

hsUnqualName :: String -> QName ()
hsUnqualName = UnQual () . hsName

hsVar :: String -> Exp ()
hsVar = Var () . hsUnqualName

hsUndefined :: Exp ()
hsUndefined = hsVar "undefined"

hsError :: String -> Exp ()
hsError s = hsVar "error" `eApp` [strE s]

cname :: CName l -> Name l
cname (VarName _ n) = n
cname (ConName _ n) = n

cloc :: CName l -> l
cloc (VarName l _) = l
cloc (ConName l _) = l

srcSpanToRange :: SrcSpan -> Range
srcSpanToRange (SrcSpan file l1 c1 l2 c2) =
  intervalToRange (toStrict $ Just $ mkRangeFile (mkAbsolute file) Nothing) $ Interval (pos l1 c1) (pos l2 c2)
  where pos l c = Pn () 0 (fromIntegral l) (fromIntegral c)

srcLocToRange :: SrcLoc -> Range
srcLocToRange (SrcLoc file l c) = srcSpanToRange (SrcSpan file l c l c)

srcSpanInfoToRange :: SrcSpanInfo -> Range
srcSpanInfoToRange = srcSpanToRange . srcInfoSpan

allUsedTypes :: Data a => a -> [Type ()]
allUsedTypes = listify (const True)

usedTypesOf :: Data a => String -> a -> [Type ()]
usedTypesOf s = listify $ (== s) . pp

uses :: Data a => String -> a -> Bool
uses ty = not . null . usedTypesOf ty

-- Fixities

insertParens :: Data a => a -> a
insertParens = everywhere (mkT $ insertPars $ fixityMap baseFixities)
  where
    fixityMap fxs = Map.fromList [ (q, fx) | fx@(Fixity _ _ q) <- fxs ]

insertPars :: Map (QName ()) Fixity -> Exp () -> Exp ()
insertPars fixs (InfixApp l e1 op e2) = InfixApp l (parL e1) op (parR e2)
  where
    getFix op = Map.lookup (qopName op) fixs
    topFix    = getFix op

    qopName (QVarOp _ x) = x
    qopName (QConOp _ x) = x

    needParen same (Just (Fixity atop top _)) (Just (Fixity achild child _))
      | top > child    = True
      | top < child    = False
      | atop /= achild = True
      | otherwise      = same atop
    needParen _ Nothing _ = True  -- If we don't know, add parens
    needParen _ _ Nothing = True

    parL = par $ needParen (AssocLeft () /=)
    parR = par $ needParen (AssocRight () /=)

    par need e@(InfixApp _ _ op _)
      | need topFix (getFix op) = Paren () e
    par _ e = e
insertPars _ e = e

-- Patterns
patToExp :: Pat l -> Maybe (Exp l)
patToExp = \case
  PVar l x            -> Just $ Var l (UnQual l x)
  PLit l s v          -> Just $ Lit l v
  PInfixApp l p f q   -> InfixApp l <$> patToExp p <*> pure (QConOp l f) <*> patToExp q
  PApp l x ps         -> foldl' (App l) (Con l x) <$> traverse patToExp ps
  PTuple l b ps       -> Tuple l b <$> traverse patToExp ps
  PUnboxedSum l i j p -> UnboxedSum l i j <$> patToExp p
  PList l ps          -> List l <$> traverse patToExp ps
  PParen l p          -> Paren l <$> patToExp p
  PAsPat _ _ p        -> patToExp p
  PIrrPat _ p         -> patToExp p
  PatTypeSig _ p _    -> patToExp p
  PBangPat _ p        -> patToExp p
  _                   -> Nothing

data Strictness = Lazy | Strict
  deriving Show
