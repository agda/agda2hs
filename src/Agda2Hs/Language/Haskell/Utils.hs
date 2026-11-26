
module Agda2Hs.Language.Haskell.Utils where

import Prelude hiding ( foldl' )

import Control.Monad ( guard )

import Data.Data ( Data, cast, toConstr )
import Data.Generics ( listify, everywhere, everything, everythingWithContext, mkQ, mkT, extQ, extT )
import Data.Generics.Twins ( gzipWithQ )
import Data.List ( find, foldl' )
import Data.Map ( Map )

import qualified Data.Map as Map

import Language.Haskell.Exts hiding ( Strict, Lazy )

import Agda.Syntax.Position

import Agda.Utils.FileName ( mkAbsolute )
import Agda.Utils.List ( initLast )
import Agda.Utils.Maybe.Strict ( toStrict )
import System.FilePath (isAbsolute)
import Agda.Utils.Maybe (boolToMaybe)

-- Names ------------------------------------------------------------------


validVarId :: String -> Bool
validVarId s = case lexTokenStream s of
  ParseOk [Loc _ VarId{}] -> True
  _ -> False

validConId :: String -> Bool
validConId s = case lexTokenStream s of
  ParseOk [Loc _ ConId{}] -> True
  _ -> False

validModuleName :: ModuleName () -> Bool
validModuleName (ModuleName _ name) = all validConId $ splitOnDot name
  where
    splitOnDot s =
      let (part, rest) = break (== '.') s
      in part : case rest of
        []      -> []
        _:parts -> splitOnDot parts

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

isOpName :: Name () -> Bool
isOpName (Symbol {}) = True
isOpName _ = False

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

-- | The name declared by a declaration head.
declHeadName :: DeclHead l -> Name l
declHeadName = \case
  DHead _ n     -> n
  DHInfix _ _ n -> n
  DHParen _ dh  -> declHeadName dh
  DHApp _ dh _  -> declHeadName dh

-- | The top-level names declared by a declaration. Type signatures, fixity
--   declarations, and instances do not declare a new entity and are ignored.
declaredNames :: Decl l -> [Name l]
declaredNames = \case
  TypeDecl _ dh _          -> [declHeadName dh]
  DataDecl _ _ _ dh _ _    -> [declHeadName dh]
  GDataDecl _ _ _ dh _ _ _ -> [declHeadName dh]
  ClassDecl _ _ dh _ _     -> [declHeadName dh]
  FunBind _ ms             -> take 1 (map definedName ms)
  PatBind _ p _ _          -> [n | PVar _ n <- [p]]
  _                        -> []

-- Alpha-equivalence --------------------------------------------------------

-- | A renaming pairing names bound in the left term with the corresponding
-- names bound in the right term.
type AlphaRenaming = [(Name (), Name ())]

-- | Compare two Haskell terms up to alpha-equivalence of locally bound names.
--
-- Local variables (pattern variables, type variables, lambda and @let@ bound
-- variables, and names bound in a @do@ block) and the names of auxiliary
-- definitions from a @where@ block may differ between the two terms.
alphaEq :: Data a => a -> a -> Bool
alphaEq = eqAlpha []

-- | Like 'alphaEq', but the names in the given renaming are treated as bound
-- and are matched according to the renaming rather than being implicitly
-- universally quantified. This is needed when comparing Haskell code in which
-- the names in question are bound by, for example, a datatype's type
-- parameters.
alphaEqWith :: Data a => AlphaRenaming -> a -> a -> Bool
alphaEqWith = eqAlpha

eqAlpha :: forall d e. (Data d, Data e) => AlphaRenaming -> d -> e -> Bool
eqAlpha ren x y
  | Just (x' :: Match ())    <- cast x, Just (y' :: Match ())    <- cast y = eqMatch ren x' y'
  | Just (x' :: Alt ())      <- cast x, Just (y' :: Alt ())      <- cast y = eqAlt ren x' y'
  | Just (x' :: Exp ())      <- cast x, Just (y' :: Exp ())      <- cast y = eqExp ren x' y'
  | Just (x' :: Type ())     <- cast x, Just (y' :: Type ())     <- cast y = eqType ren x' y'
  | Just (x' :: Decl ())     <- cast x, Just (y' :: Decl ())     <- cast y = eqDecl ren x' y'
  | Just (x' :: InstRule ()) <- cast x, Just (y' :: InstRule ()) <- cast y = eqInstRule ren x' y'
  | Just (x' :: QName ())    <- cast x, Just (y' :: QName ())    <- cast y = eqQName ren x' y'
  | Just (x' :: Name ())     <- cast x, Just (y' :: Name ())     <- cast y = eqName ren x' y'
  | otherwise = eqStruct ren x y

-- | Compare two values structurally, assuming they have the same constructor.
eqStruct :: forall d e. (Data d, Data e) => AlphaRenaming -> d -> e -> Bool
eqStruct ren x y = toConstr x == toConstr y && and (gzipWithQ (eqAlpha ren) x y)

-- | Compare two names under the given renaming. The renaming is ordered from
-- innermost to outermost binding. The first entry that mentions either name
-- determines which binder each of them refers to; if they refer to different
-- binders (or one is free and the other bound) the names are not equal.
eqName :: AlphaRenaming -> Name () -> Name () -> Bool
eqName ren x y = case find (\(x', y') -> x' == x || y' == y) ren of
  Just (x', y') -> x' == x && y' == y
  Nothing -> x == y

eqQName :: AlphaRenaming -> QName () -> QName () -> Bool
eqQName ren (UnQual _ x) (UnQual _ y) = eqName ren x y
eqQName _ x y = x == y

-- Clauses

eqMatch :: AlphaRenaming -> Match () -> Match () -> Bool
eqMatch ren (Match _ f ps rhs bnds) (Match _ g qs rhs2 bnds2) =
      eqAlpha ren f g
   && eqAlpha ren' ps qs
   && eqAlpha ren' rhs rhs2
   && eqAlpha ren' bnds bnds2
  where ren' = localBinders ps bnds qs bnds2 ++ ren
eqMatch ren (InfixMatch _ p f ps rhs bnds) (InfixMatch _ q g qs rhs2 bnds2) =
      eqAlpha ren f g
   && eqAlpha ren' (p : ps) (q : qs)
   && eqAlpha ren' rhs rhs2
   && eqAlpha ren' bnds bnds2
  where ren' = localBinders (p : ps) bnds (q : qs) bnds2 ++ ren
eqMatch _ _ _ = False

eqAlt :: AlphaRenaming -> Alt () -> Alt () -> Bool
eqAlt ren (Alt _ p rhs bnds) (Alt _ q rhs2 bnds2) =
      eqAlpha ren' p q
   && eqAlpha ren' rhs rhs2
   && eqAlpha ren' bnds bnds2
  where ren' = localBinders [p] bnds [q] bnds2 ++ ren

-- | Extend a renaming with the pattern variables of some patterns and the
-- names declared by a @where@ block.
localBinders :: [Pat ()] -> Maybe (Binds ()) -> [Pat ()] -> Maybe (Binds ()) -> AlphaRenaming
localBinders ps bnds qs bnds2 =
  zip (patBinders ps) (patBinders qs) ++ zip (bindsBinders bnds) (bindsBinders bnds2)

-- Expressions

eqExp :: AlphaRenaming -> Exp () -> Exp () -> Bool
eqExp ren (Lambda _ ps e) (Lambda _ qs f) =
      eqAlpha ren' ps qs && eqAlpha ren' e f
  where ren' = zip (patBinders ps) (patBinders qs) ++ ren
eqExp ren (Let _ bnds e) (Let _ bnds2 f) =
      eqAlpha ren' bnds bnds2 && eqAlpha ren' e f
  where ren' = zip (bindsBinders (Just bnds)) (bindsBinders (Just bnds2)) ++ ren
eqExp ren (Do _ ss) (Do _ ts) = eqDo ren ss ts
eqExp ren (MDo _ ss) (MDo _ ts) = eqDo ren ss ts
eqExp ren x y = eqStruct ren x y

eqDo :: AlphaRenaming -> [Stmt ()] -> [Stmt ()] -> Bool
eqDo ren (s : ss) (t : ts) = eqStmt ren s t && eqDo (stmtBinders s t ren) ss ts
eqDo _ [] [] = True
eqDo _ _ _ = False

eqStmt :: AlphaRenaming -> Stmt () -> Stmt () -> Bool
eqStmt ren (Generator _ p e) (Generator _ q f) =
      eqAlpha ren' p q && eqAlpha ren e f
  where ren' = zip (patBinders p) (patBinders q) ++ ren
eqStmt ren (Qualifier _ e) (Qualifier _ f) = eqAlpha ren e f
eqStmt ren (LetStmt _ bnds) (LetStmt _ bnds2) =
      eqAlpha ren' bnds bnds2
  where ren' = zip (bindsBinders (Just bnds)) (bindsBinders (Just bnds2)) ++ ren
eqStmt _ _ _ = False

-- | Extend a renaming with the names bound by a statement, for the statements
-- that follow it.
stmtBinders :: Stmt () -> Stmt () -> AlphaRenaming -> AlphaRenaming
stmtBinders (Generator _ p _) (Generator _ q _) ren =
  zip (patBinders p) (patBinders q) ++ ren
stmtBinders (LetStmt _ bnds) (LetStmt _ bnds2) ren =
  zip (bindsBinders (Just bnds)) (bindsBinders (Just bnds2)) ++ ren
stmtBinders _ _ ren = ren

-- Types

eqType :: AlphaRenaming -> Type () -> Type () -> Bool
eqType ren (TyForall _ mvs mctx t) (TyForall _ mvs2 mctx2 t2) =
      eqAlpha ren' mvs mvs2
   && eqAlpha ren' mctx mctx2
   && eqAlpha ren' t t2
  where ren' = zip (tyVarBinders mvs) (tyVarBinders mvs2) ++ freeTyVars ren x y
        x = TyForall () mvs mctx t
        y = TyForall () mvs2 mctx2 t2
eqType ren x y = eqStruct (freeTyVars ren x y) x y

-- | Extend a renaming with the free variables of two terms, which are
-- implicitly universally quantified.
freeTyVars :: (Data a, Data b) => AlphaRenaming -> a -> b -> AlphaRenaming
freeTyVars ren x y = zip (freeVars (map fst ren) x) (freeVars (map snd ren) y) ++ ren

-- | The type variables of a term that are not in the given set of bound names,
-- in order of first occurrence. Explicitly quantified variables are excluded.
freeVars :: Data a => [Name ()] -> a -> [Name ()]
freeVars bound0 = everythingWithContext bound0 (++) collect
  where
    collect :: forall a. Data a => a -> [Name ()] -> ([Name ()], [Name ()])
    collect = mkQ (\bound -> ([], bound)) collectType `extQ` collectInst

    collectType :: Type () -> [Name ()] -> ([Name ()], [Name ()])
    collectType = \case
      TyForall _ mvs _ _ -> \bound -> ([], tyVarBinders mvs ++ bound)
      TyVar _ n          -> \bound -> ([n | n `notElem` bound], bound)
      _                  -> \bound -> ([], bound)

    collectInst :: InstRule () -> [Name ()] -> ([Name ()], [Name ()])
    collectInst = \case
      IRule _ mvs _ _ -> \bound -> ([], tyVarBinders mvs ++ bound)
      _               -> \bound -> ([], bound)

-- Declarations

eqDecl :: AlphaRenaming -> Decl () -> Decl () -> Bool
eqDecl ren (PatBind _ p rhs bnds) (PatBind _ q rhs2 bnds2) =
      eqAlpha ren' p q
   && eqAlpha ren' rhs rhs2
   && eqAlpha ren' bnds bnds2
  where ren' = localBinders [p] bnds [q] bnds2 ++ ren
eqDecl ren (InstDecl _ ov ir mds) (InstDecl _ ov2 ir2 mds2) =
      eqAlpha ren' ov ov2
   && eqAlpha ren' ir ir2
   && eqAlpha ren' mds mds2
  where ren' = zip (instRuleBinders ir) (instRuleBinders ir2) ++ ren
eqDecl ren x y = eqStruct ren x y

-- Instances

eqInstRule :: AlphaRenaming -> InstRule () -> InstRule () -> Bool
eqInstRule ren (IRule _ mvs mctx ih) (IRule _ mvs2 mctx2 ih2) =
      eqAlpha ren' mvs mvs2
   && eqAlpha ren' mctx mctx2
   && eqAlpha ren' ih ih2
  where ren' = zip (tyVarBinders mvs) (tyVarBinders mvs2) ++ freeTyVars ren x y
        x = IRule () mvs mctx ih
        y = IRule () mvs2 mctx2 ih2
eqInstRule ren (IParen _ ir) (IParen _ ir2) = eqInstRule ren ir ir2
eqInstRule _ _ _ = False

instRuleBinders :: InstRule () -> [Name ()]
instRuleBinders (IRule _ mvs _ _) = tyVarBinders mvs
instRuleBinders (IParen _ ir) = instRuleBinders ir

-- Binders

patBinders :: Data a => a -> [Name ()]
patBinders = everything (++) (mkQ [] go)
  where
    go :: Pat () -> [Name ()]
    go (PVar _ n) = [n]
    go (PAsPat _ n _) = [n]
    go _ = []

tyVarBinders :: Maybe [TyVarBind ()] -> [Name ()]
tyVarBinders Nothing = []
tyVarBinders (Just vs) = concatMap go vs
  where
    go (KindedVar _ n _) = [n]
    go (UnkindedVar _ n) = [n]

bindsBinders :: Maybe (Binds ()) -> [Name ()]
bindsBinders Nothing = []
bindsBinders (Just (BDecls _ ds)) = concatMap declBinders ds
bindsBinders (Just (IPBinds _ _)) = []

declBinders :: Decl () -> [Name ()]
declBinders (PatBind _ p _ _) = patBinders p
declBinders d = declaredNames d

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
  intervalToRange (toStrict $ boolToMaybe (isAbsolute file) $ mkRangeFile (mkAbsolute file) Nothing) $ Interval () (pos l1 c1) (pos l2 c2)
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

-- Ideally, our pretty-printing library should insert parenthesis where needed.
-- However, hs-src-exts does not insert adequate parenthesis for infix
-- operators so we need to insert some by hand
-- (see issues #54 and #273 and #317 and #460).

-- | Properly parenthesize an expression with regards to the default fixities.
insertParens :: Data a => a -> a
insertParens = everywhere (mkT $ insertPars $ fixityMap baseFixities)
  where
    fixityMap fxs = Map.fromList [ (q, fx) | fx@(Fixity _ _ q) <- fxs ]

-- | Given fixities of operators, properly parenthesize an expression.
insertPars :: Map (QName ()) Fixity -> Exp () -> Exp ()
insertPars fixs = \case
  (InfixApp l e1 op e2) -> InfixApp l (parL op e1) op (parR op e2)
  (LeftSection l e1 op) -> LeftSection l (parL op e1) op
  (RightSection l op e2) -> RightSection l op (parR op e2)
  e -> e
  where
    getFix op = Map.lookup (qopName op) fixs

    qopName (QVarOp _ x) = x
    qopName (QConOp _ x) = x

    needParen same (Just (Fixity atop top _)) (Just (Fixity achild child _))
      | top > child    = True
      | top < child    = False
      | atop /= achild = True
      | otherwise      = same atop
    needParen _ Nothing _ = True  -- If we don't know, add parens
    needParen _ _ Nothing = True

    needParenExpr (InfixApp _ _ _ e2) = needParenExpr e2
    needParenExpr Lambda{} = True
    needParenExpr If{} = True
    needParenExpr _ = False

    parL topOp e =
      if needParenExpr e
      then mkParen e
      else par topOp (needParen (AssocLeft () /=)) e
    parR topOp = par topOp (needParen (AssocRight () /=))

    par topOp need e@(InfixApp _ _ op _)
      | need (getFix topOp) (getFix op) = mkParen e
    par _ _ e = e

mkParen :: Exp () -> Exp ()
mkParen e@Paren{} = e
mkParen e = Paren () e


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


-- | Add a class constraint to a Haskell type.
constrainType
  :: Asst () -- ^ The class assertion.
  -> Type () -- ^ The type to constrain.
  -> Type ()
constrainType c = \case
  TyForall _ as (Just (CxTuple _  cs)) t -> TyForall () as      (Just (CxTuple  () (c:cs))) t
  TyForall _ as (Just (CxSingle _ c')) t -> TyForall () as      (Just (CxTuple  () [c,c'])) t
  TyForall _ as Nothing                t -> TyForall () as      (Just (CxSingle () c     )) t
  t                                      -> TyForall () Nothing (Just (CxSingle () c     )) t


-- | Add explicit quantification over a variable to a Haskell type.
qualifyType
  :: TyVarBind ()  -- ^ Name of the variable.
  -> Type () -- ^ Type to quantify.
  -> Type ()
qualifyType a = \case
    TyForall _ (Just as) cs t -> TyForall () (Just (a:as)) cs      t
    TyForall _ Nothing   cs t -> TyForall () (Just [a]   ) cs      t
    t                         -> TyForall () (Just [a]   ) Nothing t

isQuantifiedAsst :: Asst () -> Bool
isQuantifiedAsst (TypeA _ TyForall{}) = True
isQuantifiedAsst (IParam _ _ TyForall{}) = True
isQuantifiedAsst _ = False
