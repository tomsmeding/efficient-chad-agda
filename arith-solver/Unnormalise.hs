{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
module Unnormalise where

import Data.Bifunctor (first)

import Debug.Trace

import AST


unnormaliseContext :: KnownAbs abs => AgdaContext abs -> AgdaContext abs
unnormaliseContext = mapExpr unnormalise . traceShowId

unnormalise :: KnownAbs abs => Expr abs -> Expr abs
unnormalise = \case
  BOp (Call (Var "sign") [e]) ApplySign rhs
    | (es, Lit 0) <- collectAddNats rhs
    , all (== UOp Abs e) es
    -> BOp (UOp Pos (Lit (fromIntegral (length es)))) Mul (unnormalise e)

  BOp (Var "Data.Sign.Base.Sign.+") ApplySign rhs
    | (es@(e1 : erest), Lit 0) <- collectAddNats rhs
    , all (== e1) erest
    -> BOp (UOp Pos (Lit (fromIntegral (length es)))) Mul (UOp Pos (unnormalise e1))

  UOp Pos (BOp e1 AddNat e2) ->
    BOp (unnormalise (UOp Pos e1)) Add (unnormalise (UOp Pos e2))

  UOp Pos (Call (Var "ℕ.suc") [e]) ->
    BOp (UOp Pos (Lit 1)) Add (unnormalise (UOp Pos e))

  e -> recurse unnormalise e

collectAddNats :: Expr abs -> ([Expr abs], Expr abs)
collectAddNats (BOp a AddNat b) = first (a :) (collectAddNats b)
collectAddNats e = ([], e)
