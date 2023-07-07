{-# LANGUAGE LambdaCase #-}
module ToSMT where

import Data.Char (isAlphaNum, ord, isAscii)
import Data.Foldable (toList)
import Data.Maybe (mapMaybe)

import AST


contextToSMT :: AAgdaContext -> String
contextToSMT ctx@(Context goal givens vals) =
  let vars = allVarsContext ctx
  in unlines $
       map varDecl (toList vars)
       ++ mapMaybe (uncurry assertGiven) givens
       ++ map (uncurry assertValue) vals
       ++ [assertNotGoal goal
          ,"(check-sat)"]

assertGiven :: Name -> AExpr -> Maybe String
assertGiven name e
  | isBoolean e = Just $ "(assert " ++ expr e ")  ; " ++ name
  | otherwise = Nothing

assertValue :: Name -> AExpr -> String
assertValue name e = "(assert (= " ++ mangle name ++ " " ++ expr e "))  ; " ++ name

assertNotGoal :: AExpr -> String
assertNotGoal e
  | isBoolean e = "(assert (not " ++ expr e "))"
  | otherwise = error "Goal is not a boolean expression"

isBoolean :: AExpr -> Bool
isBoolean (BOp _ Leq _) = True
isBoolean (BOp _ Eq _) = True
isBoolean _ = False

expr :: AExpr -> ShowS
expr = \case
  BOp e1 op e2 -> binop op (expr e1) (expr e2)
  UOp op e -> unop op (expr e)
  Var n -> showString (mangle n)
  Lit x -> shows x

binop :: ABOp -> ShowS -> ShowS -> ShowS
binop op e1 e2 = case op of
  Add -> showString "(+ "  . e1 . showString " " . e2 . showString ")"
  Sub -> showString "(- "  . e1 . showString " " . e2 . showString ")"
  Mul -> showString "(* "  . e1 . showString " " . e2 . showString ")"
  Leq -> showString "(<= " . e1 . showString " " . e2 . showString ")"
  Eq  -> showString "(= "  . e1 . showString " " . e2 . showString ")"
  ExprAdd -> error "ToSMT: unexpected expression operator"
  ExprSub -> error "ToSMT: unexpected expression operator"
  ExprMul -> error "ToSMT: unexpected expression operator"
  ExprEq -> error "ToSMT: unexpected expression operator"

unop :: AUOp -> ShowS -> ShowS
unop op e = case op of
  Pos -> e
  Neg -> showString "(~ " . e . showString ")"
  ExprNeg -> error "ToSMT: unexpected expression operator"

varDecl :: Name -> String
varDecl n = "(declare-fun " ++ mangle n ++ " () Int" ++ ")"

mangle :: Name -> String
mangle = (('v' :) .) . concatMap $ \c ->
  if isAlphaNum c && isAscii c
    then [c]
    else '_' : show (ord c) ++ "_"
