{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Abstract (abstractContext) where

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer.CPS
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import AST


type M = ReaderT (Set Name)
         (StateT Int
         (StateT (Map FExpr Name)
         (Writer (Map Name FExpr))))

genName :: M Name
genName = lift $ state (\i -> ('x' : show i, i + 1))

genSatisfy :: M a -> (a -> Bool) -> M a
genSatisfy act pr = do
  x <- act
  if pr x then return x else genSatisfy act pr

abstractContext :: AgdaContext 'Full -> (Map Name FExpr, AgdaContext 'Abstr)
abstractContext ctx =
  swap . runWriter $
  flip evalStateT mempty $
  flip evalStateT 0 $
  flip runReaderT (allVarsContext ctx) $
    mapExprA abstract' ctx
  where swap (x, y) = (y, x)

abstract' :: FExpr -> M (Expr 'Abstr)
abstract' expr = case expr of
  BOp _ op _
    | op `elem` [Add, Sub, Mul, Leq, Eq] -> preserve
    | otherwise -> forget
  UOp op _
    | op `elem` [Pos, Neg] -> preserve
    | otherwise -> forget
  Call{} -> forget
  Lam{} -> forget
    -- where
    --   withinScope :: Name -> M a -> M a
    --   withinScope n = local (Set.insert n)
  OpaqueArg{} -> forget
  Var{} -> preserve
  Lit{} -> preserve
  where
    preserve = recurseA abstract' expr
    forget = do
      yet <- lift $ lift $ get
      case Map.lookup expr yet of
        Nothing -> do
          avoid <- ask
          name <- genSatisfy genName (`Set.notMember` avoid)
          lift $ lift $ modify (Map.insert expr name)
          lift $ lift $ lift $ tell (Map.singleton name expr)
          return (Var name)
        Just name ->
          return (Var name)
