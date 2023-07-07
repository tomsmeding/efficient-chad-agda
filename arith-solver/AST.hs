{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
module AST where

import Data.Functor.Const
import Data.Functor.Identity
import Data.Set (Set)
import qualified Data.Set as Set
import Text.Parsec.Expr (Assoc(..))

import Util
import Data.Maybe (fromJust)


data Abstracted = Full | Abstr
  deriving (Show)

data SAbstracted abs where
  SFull :: SAbstracted 'Full
  SAbstr :: SAbstracted 'Abstr

class KnownAbs abs where knownAbs :: SAbstracted abs
instance KnownAbs 'Full where knownAbs = SFull
instance KnownAbs 'Abstr where knownAbs = SAbstr


type Name = String

data AgdaContext abs =
  Context (Expr abs)  -- ^ goal
          [(Name, Expr abs)]  -- ^ types of givens
          [(Name, Expr abs)]  -- ^ values of integer-typed givens
  deriving (Show)
deriving instance Read AAgdaContext
deriving instance Read FAgdaContext

data Expr abs where
  BOp :: Expr abs -> BOp abs -> Expr abs -> Expr abs
  UOp :: UOp abs -> Expr abs -> Expr abs
  Call :: Expr 'Full -> [Expr 'Full] -> Expr 'Full
  Lam :: Maybe Name -> Expr 'Full -> Expr 'Full
  OpaqueArg :: String -> Expr 'Full
  Var :: Name -> Expr abs
  Lit :: Integer -> Expr abs

deriving instance Show (Expr abs)
deriving instance Read FExpr
deriving instance Eq (Expr abs)
deriving instance Ord (Expr abs)
instance Read (Expr 'Abstr) where
  readsPrec d s = case traverse (firstF convertExpr) (readsPrec @FExpr d s) of
                    Nothing -> error "read @AExpr: expression was actually full, not abstract"
                    Just x -> x

data BOp abs where
  Add, Sub, Mul :: BOp abs
  Leq       :: BOp abs  -- ≤
  Eq        :: BOp abs  -- ≡
  ExprAdd   :: BOp abs  -- #+
  ExprSub   :: BOp abs  -- :-
  ExprMul   :: BOp abs  -- #*
  ExprEq    :: BOp abs  -- :=
  AddNat    :: BOp 'Full  -- +ℕ
  Arrow     :: BOp 'Full  -- ->
  ApplySign :: BOp 'Full  -- ◃
  Pair      :: BOp 'Full  -- ,
  Cons      :: BOp 'Full  -- ∷
  KnownOp   :: String -> BOp 'Full

deriving instance Show (BOp abs)
deriving instance Read (BOp 'Full)
deriving instance Eq (BOp abs)
deriving instance Ord (BOp abs)

data UOp abs where
  Pos, Neg :: UOp abs
  Abs :: UOp 'Full
  ExprNeg :: UOp abs  -- :-

deriving instance Show (UOp abs)
deriving instance Read (UOp 'Full)
deriving instance Eq (UOp abs)
deriving instance Ord (UOp abs)

data OpInfo = OpPrefix [String] (UOp 'Full)
            | OpInfix [String] (BOp 'Full) Assoc

type FAgdaContext = AgdaContext 'Full
type AAgdaContext = AgdaContext 'Abstr
type FExpr = Expr 'Full
type AExpr = Expr 'Abstr
type FBOp = BOp 'Full
type ABOp = BOp 'Abstr
type FUOp = UOp 'Full
type AUOp = UOp 'Abstr

operatorTable :: [[OpInfo]]
operatorTable =
  [[OpPrefix ["+"] Pos]  -- ?
  ,[OpInfix [":*"] (KnownOp ":*") AssocLeft  -- custom operators, highest
   ,OpInfix [":*!"] (KnownOp ":*!") AssocLeft
   ,OpInfix [":+"] (KnownOp ":+") AssocLeft
   ,OpInfix [":+!"] (KnownOp ":+!") AssocLeft
   ,OpInfix [":->"] (KnownOp ":->") AssocLeft]
  ,[OpPrefix [":-"] ExprNeg]  -- 9
  ,[OpPrefix ["-"] Neg  -- 8
   ,OpInfix ["#*"] ExprMul AssocLeft]
  ,[OpInfix ["*"] Mul AssocLeft  -- 7
   ,OpInfix ["#+"] ExprAdd AssocLeft
   ,OpInfix [":-"] ExprSub AssocLeft]
  ,[OpInfix ["+"] Add AssocLeft  -- 6
   ,OpInfix ["+ℕ"] AddNat AssocLeft
   ,OpInfix ["-"] Sub AssocLeft]
  ,[OpInfix ["◃"] ApplySign AssocNone  -- 5
   ,OpInfix ["∷"] Cons AssocRight]
  ,[OpInfix ["≤"] Leq AssocNone  -- 4
   ,OpInfix ["≡"] Eq AssocNone
   ,OpInfix [","] Pair AssocRight
   ,OpInfix [":="] ExprEq AssocNone]
  ,[OpPrefix ["∣_∣"] Abs]  -- a gross hack to provide a pretty-printed version of this
  ,[OpInfix ["→", "->"] Arrow AssocRight]  -- special syntax, lowest
  ]

mapExpr :: (Expr abs -> Expr abs') -> AgdaContext abs -> AgdaContext abs'
mapExpr f = runIdentity . mapExprA (Identity . f)

mapExprA :: Applicative f => (Expr abs -> f (Expr abs')) -> AgdaContext abs -> f (AgdaContext abs')
mapExprA f (Context goal env zvars) =
  Context <$> f goal <*> traverse (secondF f) env <*> traverse (secondF f) zvars

recurse :: KnownAbs abs' => (Expr abs -> Expr abs') -> Expr abs -> Expr abs'
recurse f = runIdentity . recurseA (Identity . f)

recurseA :: forall abs' abs f. (KnownAbs abs', Applicative f) => (Expr abs -> f (Expr abs')) -> Expr abs -> f (Expr abs')
recurseA f = \case
  BOp e1 op e2 -> case convertBOp op of
                    Just op' -> BOp <$> f e1 <*> pure op' <*> f e2
                    Nothing -> error $ "recurseA: Mapping into Abstr but recursing on " ++ show op
  UOp op e -> case convertUOp op of
                Just op' -> UOp op' <$> f e
                Nothing -> error $ "recurseA: Mapping into Abstr but recursing on " ++ show op
  Call e es -> case knownAbs @abs' of
                 SFull -> Call <$> f e <*> traverse f es
                 SAbstr -> error "recurseA: Mapping into Abstr but recursing on Call"
  Lam n e -> case knownAbs @abs' of
               SFull -> Lam n <$> f e
               SAbstr -> error "recurseA: Mapping into Abstr but recursing on Lam"
  OpaqueArg s -> case knownAbs @abs' of
                   SFull -> pure (OpaqueArg s)
                   SAbstr -> error "recurseA: Mapping into Abstr but recursing on OpaqueArg"
  Var n -> pure (Var n)
  Lit x -> pure (Lit x)

allVarsContext :: KnownAbs abs => AgdaContext abs -> Set Name
allVarsContext ctx@(Context _ givens zvars) =
  getConst (mapExprA (Const . allVars) ctx)
    <> Set.fromList (map fst givens)
    <> Set.fromList (map fst zvars)

allVars :: forall abs. KnownAbs abs => Expr abs -> Set Name
allVars = \case
  Var n -> Set.singleton n
  e -> getConst (recurseA @abs (Const . allVars) e)

freeVars :: Expr abs -> Set Name
freeVars = \case
  BOp e1 _ e2 -> freeVars e1 <> freeVars e2
  UOp _ e -> freeVars e
  Call e es -> freeVars e <> foldMap freeVars es
  Lam (Just n) e -> Set.delete n (freeVars e)
  Lam Nothing e -> freeVars e
  OpaqueArg _ -> mempty
  Var n -> Set.singleton n
  Lit _ -> mempty

convertBOp :: forall abs abs'. KnownAbs abs' => BOp abs -> Maybe (BOp abs')
convertBOp = \case
  Add -> Just Add
  Sub -> Just Sub
  Mul -> Just Mul
  Leq -> Just Leq
  Eq  -> Just Eq
  ExprAdd -> Just ExprAdd
  ExprSub -> Just ExprSub
  ExprMul -> Just ExprMul
  ExprEq -> Just ExprEq
  AddNat -> check AddNat
  Arrow -> check Arrow
  ApplySign -> check ApplySign
  Pair -> check Pair
  Cons -> check Cons
  KnownOp s -> check (KnownOp s)
  where
    check :: KnownAbs abs' => BOp 'Full -> Maybe (BOp abs')
    check op = case knownAbs @abs' of
                 SFull -> Just op
                 SAbstr -> Nothing

convertUOp :: forall abs abs'. KnownAbs abs' => UOp abs -> Maybe (UOp abs')
convertUOp = \case
  Pos -> Just Pos
  Neg -> Just Neg
  Abs -> check Abs
  ExprNeg -> Just ExprNeg
  where
    check :: KnownAbs abs' => UOp 'Full -> Maybe (UOp abs')
    check op = case knownAbs @abs' of
                 SFull -> Just op
                 SAbstr -> Nothing

injectBOp :: BOp 'Abstr -> BOp 'Full
injectBOp = fromJust . convertBOp

injectUOp :: UOp 'Abstr -> UOp 'Full
injectUOp = fromJust . convertUOp

convertExpr :: FExpr -> Maybe AExpr
convertExpr = \case
  BOp e1 op e2 -> BOp <$> convertExpr e1 <*> convertBOp op <*> convertExpr e2
  UOp op e -> UOp <$> convertUOp op <*> convertExpr e
  Call{} -> Nothing
  Lam{} -> Nothing
  OpaqueArg{} -> Nothing
  Var n -> pure (Var n)
  Lit x -> pure (Lit x)

injectExpr :: AExpr -> FExpr
injectExpr = \case
  BOp e1 op e2 -> BOp (injectExpr e1) (injectBOp op) (injectExpr e2)
  UOp op e -> UOp (injectUOp op) (injectExpr e)
  Var n -> Var n
  Lit x -> Lit x

freshVar :: KnownAbs abs => [Expr abs] -> String
freshVar es =
  let taken = foldMap allVars es
  in head $ filter (`Set.notMember` taken) ("x" : "y" : "z" : "a" : ['x' : show i | i <- [1::Int ..]])
