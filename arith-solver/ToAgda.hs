{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GADTs #-}
module ToAgda (exprToAgda, exprToAgdaInArg) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe)
import Text.Parsec.Expr (Assoc(..))

import AST


exprToAgda :: KnownAbs abs => Expr abs -> String
exprToAgda e = prettyExpr 0 e ""

exprToAgdaInArg :: KnownAbs abs => Expr abs -> String
exprToAgdaInArg e = prettyExpr InArg e ""

data Precedence = Finite Int | InArg
  deriving (Show, Eq, Ord)

instance Num Precedence where
  Finite n + Finite m = Finite (n + m)
  _ + _ = InArg
  Finite n * Finite m = Finite (n * m)
  _ * _ = InArg
  abs (Finite n) = Finite (abs n)
  abs InArg = InArg
  signum (Finite n) = Finite (signum n)
  signum InArg = 1
  negate (Finite n) = Finite (-n)
  negate InArg = error "negate InArg"
  fromInteger = Finite . fromInteger

prettyExpr :: KnownAbs abs => Precedence -> Expr abs -> ShowS
prettyExpr d = \case
  BOp e1 op e2 -> case fromMaybe (error $ "Not found in optableB: " ++ show op) (optableB Map.!? op) of
    (pr, AssocLeft, s)  -> combine pr s pr (pr + 1)
    (pr, AssocRight, s) -> combine pr s (pr + 1) pr
    (pr, AssocNone, s)  -> combine pr s (pr + 1) (pr + 1)
    where
      combine pr s d1 d2 = showParen (d > Finite pr) $
        prettyExpr (Finite d1) e1
        . showString (" " ++ s ++ " ")
        . prettyExpr (Finite d2) e2

  UOp op e ->
    let (pr, s) = fromMaybe (error $ "Not found in optableP: " ++ show op) (optableP Map.!? op)
    in showParen (d >= Finite pr) $
         showString (s ++ " ") . prettyExpr (Finite pr) e

  Call e1 es -> showParen (d >= InArg) $
    prettyExpr InArg e1
    . foldr (.) id (map (showString " " .) (map (prettyExpr InArg) es))

  Lam name e -> showParen (d > 0) $
    showString ("λ " ++ maybe "_" id name ++ " → ") . prettyExpr 0 e

  OpaqueArg s -> showParen (d > 0) $ showString s

  Var name -> showString name

  Lit x -> shows x

optableB :: KnownAbs abs => Map (BOp abs) (Int, Assoc, String)
optableB = Map.fromList $
  concatMap (concatMap (\case
        (OpInfix (s:_) bop assoc, pr)
          | Just bop' <- convertBOp bop -> [(bop', (pr, assoc, s))]
        _ -> []))
    (zipWith (\l i -> map (,i) l) operatorTable [maxprec, maxprec-1 ..])
  where maxprec = length operatorTable

optableP :: KnownAbs abs => Map (UOp abs) (Int, String)
optableP = Map.fromList $
  concatMap (concatMap (\case
        (OpPrefix (s:_) uop, pr)
          | Just uop' <- convertUOp uop -> [(uop', (pr, s))]
        _ -> []))
    (zipWith (\l i -> map (,i) l) operatorTable [maxprec, maxprec-1 ..])
  where maxprec = length operatorTable
