{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
module Tactic where

import Control.Applicative (liftA2)
import Control.Monad.Trans.State.Strict
import Data.Bifunctor (second, first)
import Data.Char (chr, ord, isSpace)
import Data.Function (on)
import Data.List (foldl1', foldl', sortBy, groupBy)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map.Strict (Map)
import Data.Monoid (Sum(..))
import Data.Ord (comparing)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import qualified Text.Parsec as P

-- import Debug.Trace

import AST
import Reexpress


newtype Proof = Proof FExpr
  deriving (Show)

-- | Given a context, compute a new context and a mapping from a proof of the
-- new goal to a proof of the original goal.
newtype Tactic = Tactic (AAgdaContext -> Either String (AAgdaContext, Proof -> Proof))

-- | Given a goal, compute a proof for that goal with no remaining obligations.
newtype Tactic' = Tactic' (AAgdaContext -> Either String Proof)

-- | Specialisation of a 'Tactic' that does not modify the context.
newtype GoalTactic = GoalTactic (AAgdaContext -> Either String (AExpr, Proof -> Proof))

fromGoalTactic :: GoalTactic -> Tactic
fromGoalTactic (GoalTactic f) = Tactic (\ctx@(Context _ givens zvars) -> first (\goal -> Context goal givens zvars) <$> f ctx)

instance Semigroup Tactic where
  Tactic f <> Tactic g = Tactic $ \goal -> do
    (goal1, pf1) <- f goal
    (goal2, pf2) <- g goal1
    return (goal2, pf1 . pf2)

instance Monoid Tactic where
  mempty = Tactic (\goal -> Right (goal, id))

partialTactics :: Map String ([Name] -> Either String Tactic)
partialTactics = Map.fromList
  [("norm", \_ -> Right (fromGoalTactic tNormalise))
  ,("sub", fixedArguments "sub" (SS SZ) (fromGoalTactic . tSubtract))
  ,("abs", Right . tAbstract)
  ,("rew", fixedArguments "rew" (SS SZ) (fromGoalTactic . tRewrite))]

finalTactics :: Map String ([Name] -> Either String Tactic')
finalTactics = Map.fromList
  [("exact", fixedArguments "exact" (SS SZ) tExact)
  ,("trivial", \_ -> Right tTrivial)
  ,("hole", \_ -> Right tHole)]

data Nat = Z | S Nat
  deriving (Show)
data SNat n where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)
type family NArgs n a r where
  NArgs 'Z a r = r
  NArgs ('S n) a r = a -> NArgs n a r

-- Left (required, given)
supply :: SNat n -> NArgs n a r -> [a] -> Either (Int, Int) r
supply SZ f [] = Right f
supply SZ _ l = Left (0, length l)
supply (SS n) f (x:xs) = first (first (+1)) (supply n (f x) xs)
supply (SS n) _ [] = Left (sn2int (SS n), 0)
  where sn2int :: SNat n -> Int
        sn2int SZ = 0
        sn2int (SS m) = 1 + sn2int m

fixedArguments :: String -> SNat n
               -> (NArgs n Name r)
               -> [Name] -> Either String r
fixedArguments tacname n f l =
  case supply n f l of
    Right res -> Right res
    Left (req, given) -> Left $ tacname ++ " requires " ++ show req ++ " arguments but was given " ++ show given

parseTacticString :: String -> Either String ([Tactic], Maybe Tactic')
parseTacticString str = first show (P.parse pTop "" str)
  where
    pTop = do
      list <- pList
      let validate ((_, Left t) : ts@(_:_)) = first (t :) <$> validate ts
          validate ((name, Right _) : (_:_)) =
            fail $ "Tactic ++ '" ++ name ++ "' is a final tactic but used in non-final position"
          validate [(_, Left t)] = return ([t], Nothing)
          validate [(_, Right t)] = return ([], Just t)
          validate [] = return ([], Nothing)
      validate list
    pList = pTac' `P.sepBy` (P.spaces >> P.char ';')
    pTac' = do
      (name, args) <- pTac
      case (Map.lookup name partialTactics, Map.lookup name finalTactics) of
        (Just f, _) -> case f args of
                         Left err -> fail $ "Tactic '" ++ name ++ "': " ++ err
                         Right t -> return (name, Left t)
        (_, Just f) -> case f args of
                         Left err -> fail $ "Tactic '" ++ name ++ "': " ++ err
                         Right t -> return (name, Right t)
        _ -> fail $ "Unknown tactic '" ++ name ++ "'"
    pTac = do
      let isWordChar c = not (isSpace c) && c `notElem` ";(){}:"
          pWord = P.many1 (P.satisfy isWordChar)
      cmd <- P.try $ P.spaces >> pWord
      args <- P.many (P.try (P.spaces >> pWord))
      return (cmd, args)

tExact :: Name -> Tactic'
tExact name = Tactic' $ \(Context goal givens _) ->
  case lookup name givens of
    Just rhs ->
      if goal == rhs
       then Right (Proof (Var name))
       else Left $ "exact: Definition of '" ++ name ++ "' does not equal goal"
    Nothing -> Left $ "exact: Name not found in givens: " ++ name

data ArithExpr
  = AAAdd ArithExpr ArithExpr
  | AASub ArithExpr ArithExpr
  | AAMul ArithExpr ArithExpr
  | AANeg ArithExpr
  | AALit Integer
  | AAExpr AExpr
  deriving (Show, Eq, Ord)

toArithExpr :: AExpr -> ArithExpr
toArithExpr = \case
  BOp e1 Add e2 -> AAAdd (toArithExpr e1) (toArithExpr e2)
  BOp e1 Sub e2 -> AASub (toArithExpr e1) (toArithExpr e2)
  BOp e1 Mul e2 -> AAMul (toArithExpr e1) (toArithExpr e2)
  UOp Neg e -> AANeg (toArithExpr e)
  UOp Pos (Lit n) -> AALit n
  e -> AAExpr e

fromAAnormal :: ArithExpr -> AExpr
fromAAnormal = \case
  AAAdd e1 e2 -> BOp (fromAAnormal e1) Add (fromAAnormal e2)
  AASub e1 e2 -> BOp (fromAAnormal e1) Sub (fromAAnormal e2)
  AAMul e1 e2 -> BOp (fromAAnormal e1) Mul (fromAAnormal e2)
  AANeg e -> UOp Neg (fromAAnormal e)
  AALit n | n >= 0 -> UOp Pos (Lit n)
          | otherwise -> UOp Neg (UOp Pos (Lit n))
  AAExpr e -> e

fromAAsymbolic :: ArithExpr -> FExpr
fromAAsymbolic = \case
  AAAdd e1 e2 -> BOp (fromAAsymbolic e1) ExprAdd (fromAAsymbolic e2)
  AASub e1 e2 -> BOp (fromAAsymbolic e1) ExprSub (fromAAsymbolic e2)
  AAMul e1 e2 -> BOp (fromAAsymbolic e1) ExprMul (fromAAsymbolic e2)
  AANeg e -> UOp ExprNeg (fromAAsymbolic e)
  AALit n | n >= 0 -> Call (Var "con") [UOp Pos (Lit n)]
          | otherwise -> Call (Var "con") [UOp Neg (UOp Pos (Lit n))]
  AAExpr e -> injectExpr e

-- Constant plus sum of constant times product
type SOP_AA = (Sum Integer, [(Integer, NonEmpty AExpr)])

normAA :: ArithExpr -> ArithExpr
normAA = \e -> case sortSOP . dedupSOP . toSOP 1 $ e of
                 (Sum cnst, []) -> AALit cnst
                 (Sum 0, l) -> foldl1' AAAdd (map render l)
                 (Sum cnst, l) -> foldl' AAAdd (AALit cnst) (map render l)
  where
    render :: (Integer, NonEmpty AExpr) -> ArithExpr
    render (cnst, e :| es) = case cnst of
      1  -> prod'
      -1 -> AANeg prod'
      n  -> AAMul (AALit n) prod'
      where prod' = foldl' AAMul (AAExpr e) (map AAExpr es)

    sortSOP :: SOP_AA -> SOP_AA
    sortSOP (n, l) =
      (n, sortBy (comparing snd <> comparing fst) (map (second NE.sort) l))

    dedupSOP :: SOP_AA -> SOP_AA
    dedupSOP = second $
      filter ((/= 0) . fst)
      . map ((,) <$> sum . map fst <*> snd . head)
      . groupBy ((==) `on` snd)
      . sortBy (comparing snd)

    toSOP :: Integer -> ArithExpr -> SOP_AA
    toSOP mult = \case
      AAAdd a b -> toSOP mult a <> toSOP mult b
      AASub a b -> toSOP mult a <> toSOP (-mult) b
      AAMul a b ->
        let (Sum n, terms1) = toSOP mult a  -- recurse with the signed multiplier in only one branch so the multiplication attains the correct sign
            (Sum m, terms2) = toSOP (abs mult) b
        in (Sum (n * m), [])
           <> (0, map (first (n *)) terms2)
           <> (0, map (first (* m)) terms1)
           <> mconcat
                [(0, [(c1 * c2, fs1 <> fs2)])
                | (c1, fs1) <- terms1
                , (c2, fs2) <- terms2]
      AANeg a -> toSOP (-mult) a
      AAExpr e | mult == 0 -> (0, [])
               | otherwise -> (0, [(mult, e :| [])])
      AALit n -> (Sum (mult * n), [])

nameAA :: ArithExpr -> ([(AExpr, Name)], ArithExpr)
nameAA = \expr ->
  let (named, (mp, _)) = runState (go expr) (mempty, 0)
  in (reverse mp, named)
  where
    go :: ArithExpr -> State ([(AExpr, Name)], Int) ArithExpr
    go (AAAdd a b) = liftA2 AAAdd (go a) (go b)
    go (AASub a b) = liftA2 AASub (go a) (go b)
    go (AAMul a b) = liftA2 AAMul (go a) (go b)
    go (AANeg a) = AANeg <$> go a
    go (AALit x) = pure (AALit x)
    go (AAExpr e) = state $ \(mp, i) ->
      case lookup e mp of
        Just name -> (AAExpr (Var name), (mp, i))
        Nothing ->
          let name | i < 26 = [chr (ord 'a' + i)]
                   | otherwise = 'a' : show (i - 25)
          in (AAExpr (Var name), ((e, name) : mp, i + 1))

replaceAA :: [(AExpr, AExpr)] -> ArithExpr -> ArithExpr
replaceAA mp = \case
  AAAdd a b -> AAAdd (replaceAA mp a) (replaceAA mp b)
  AASub a b -> AASub (replaceAA mp a) (replaceAA mp b)
  AAMul a b -> AAMul (replaceAA mp a) (replaceAA mp b)
  AANeg a -> AANeg (replaceAA mp a)
  AALit x -> AALit x
  AAExpr e -> case lookup e mp of
                Nothing -> AAExpr e
                Just e' -> AAExpr e'

-- | Given an arithmetic expression e, return:
-- 1. an arithmetic expression e' (the normalised version of e)
-- 2. a term of type (e' ≡ e).
makeNormaliseProof :: AExpr -> (AExpr, FExpr)
makeNormaliseProof old =
  let oldAA = toArithExpr old
      newAA = normAA oldAA
      (nameMapping, oldAAabs) = nameAA oldAA
      (varvalues, variables) = unzip nameMapping
      oldSymAbs = fromAAsymbolic oldAAabs
      new = fromAAnormal newAA
      newAAabs = replaceAA (map (second Var) nameMapping) newAA
      newSymAbs = fromAAsymbolic newAAabs
      equation = BOp newSymAbs ExprEq oldSymAbs
      lam = foldr Lam equation (map Just variables)
      eqprf = Call (Var "solve")
                (Lit (fromIntegral (length variables))
                : lam
                : Var "refl"
                : map injectExpr varvalues)
  in (new, eqprf)

tNormalise :: GoalTactic
tNormalise = GoalTactic $ \(Context goal _ _) ->
  case goal of
    BOp old1 Leq old2 ->
      let (new1, eqprf1) = makeNormaliseProof old1
          (new2, eqprf2) = makeNormaliseProof old2
          goal' = BOp new1 Leq new2
          substvar = freshVar [old2, new1]
          congcong (Proof newprf) = Proof $
            Call (Var "subst")
              [Lam (Just substvar) (BOp (Var substvar) Leq (injectExpr old2))
              ,eqprf1
              ,Call (Var "subst")
                 [Lam (Just substvar) (BOp (injectExpr new1) Leq (Var substvar))
                 ,eqprf2
                 ,newprf]]
      in Right (goal', congcong)
    _ -> Left "normalise: Goal was not of the form a ≤ b"

tSubtract :: Name -> GoalTactic
tSubtract name = GoalTactic $ \(Context goal givens _) -> do
  given <- case lookup name givens of
    Just given -> Right given
    Nothing -> Left $ "sub: Name not found in givens: " ++ name

  (givenL, givenR) <- case given of
    BOp e1 Leq e2 -> return (e1, e2)
    _ -> Left $ "sub: Given '" ++ name ++ "' not of the form a ≤ b"

  (goalL, goalR) <- case goal of
    BOp e1 Leq e2 -> return (e1, e2)
    _ -> Left $ "sub: Goal not of the form a ≤ b"

  return (BOp (BOp goalL Sub givenL) Leq (BOp goalR Sub givenR)
         ,\(Proof prf) ->
             let eqprf a b =
                   Call (Var "solve")
                     [Lit 2
                     ,Lam (Just "a") $ Lam (Just "b") $
                        BOp (BOp (BOp (Var "a") ExprSub (Var "b")) ExprAdd (Var "b")) ExprEq (Var "a")
                     ,Var "refl", injectExpr a, injectExpr b]
                 substvar = freshVar [goalL, goalR, givenR]
             -- cong (\y -> _ ≤ y) (solve 2 (\a b -> a :- b :+ b := a) refl goalR givenR)
             --   (cong (\x -> x ≤ _) (solve 2 (\a b -> a :- b :+ b := a) refl goalL givenL)
             --     (+-mono-≤ prf given))
             in Proof $ Call (Var "subst")
                          [Lam (Just substvar) (BOp (injectExpr $ goalL) Leq (Var substvar)), eqprf goalR givenR
                          ,Call (Var "subst")
                             [Lam (Just substvar) (BOp (Var substvar) Leq (injectExpr $ BOp (BOp goalR Sub givenR) Add givenR)), eqprf goalL givenL
                             ,Call (Var "+-mono-≤") [prf, Var name]]])

tAbstract :: [Name] -> Tactic
tAbstract names = Tactic $ \ctx -> do
  ctx' <- backsubstituteContext names ctx
  return (ctx', id)

tRewrite :: Name -> GoalTactic
tRewrite givenname = GoalTactic $ \(Context goal givens _) ->
  case lookup givenname givens of
    Just (BOp lhs Eq rhs) ->
      let (goal', ctxfun) = replace lhs rhs goal
          substvar = freshVar [rhs, goal]
      in Right (goal', \(Proof prf) -> Proof $ Call (Var "subst") [Lam (Just substvar) (ctxfun (Var substvar)), Call (Var "sym") [Var givenname], prf])
    Just _ ->Left $ "sub: Given '" ++ givenname ++ "' not of the form a ≡ b"
    Nothing -> Left $ "rew: Name not found in givens: " ++ givenname
  where
    replace :: AExpr -> AExpr -> AExpr -> (AExpr, FExpr -> FExpr)
    replace needle repl subj
      | subj == needle = (repl, id)
      | otherwise = case subj of
          BOp e1 op e2 ->
            let (e1', f1) = replace needle repl e1
                (e2', f2) = replace needle repl e2
            in (BOp e1' op e2', BOp <$> f1 <*> pure (injectBOp op) <*> f2)
          UOp op e ->
            let (e', f) = replace needle repl e
            in (UOp op e', UOp (injectUOp op) <$> f)
          Var n -> (Var n, \_ -> Var n)
          Lit x -> (Lit x, \_ -> Lit x)

tTrivial :: Tactic'
tTrivial = Tactic' $ \(Context goal _ _) ->
  case goal of
    BOp a Leq b
      | Just a' <- fromLiteral a
      , Just b' <- fromLiteral b
      , a' <= b'
      -> Right (Proof (Call (Var "≤ᵇ⇒≤") [Var "tt"]))
    _ -> Left "Goal is not trivial"
  where
    fromLiteral :: AExpr -> Maybe Integer
    fromLiteral (Lit x) = Just x
    fromLiteral (UOp Pos e) = fromLiteral e
    fromLiteral (UOp Neg e) = negate <$> fromLiteral e
    fromLiteral _ = Nothing

tHole :: Tactic'
tHole = Tactic' $ \_ -> Right (Proof (Var "?"))
