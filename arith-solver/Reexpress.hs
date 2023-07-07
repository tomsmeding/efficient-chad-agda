{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
module Reexpress (
  reexpressContext,
  backsubstituteContext,
) where

import Data.Bifunctor (second)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set

import AST


replace :: KnownAbs abs => Map (Expr abs) (Expr abs) -> Expr abs -> Expr abs
replace mp e
  | Just e' <- Map.lookup e mp = e'
  | otherwise = recurse (replace mp) e

-- | Backsubstitute all zvars that mention one of the names into the givens and the goal.
reexpressContext :: KnownAbs abs => [Name] -> AgdaContext abs -> AgdaContext abs
reexpressContext absvars (Context goal givens zvars) =
  let absvars' = Set.fromList absvars
      hasAbsvar = not . Set.null . Set.intersection absvars'
      suitablezvars = filter (hasAbsvar . allVars . snd) zvars
  in case backsubstituteContext (map fst suitablezvars) (Context goal givens zvars) of
       Left err -> error $ "Unexpected: " ++ err
       Right r -> r

-- | Backsubstitute the given variables into the givens and the goal.
backsubstituteContext :: KnownAbs abs => [Name] -> AgdaContext abs -> Either String (AgdaContext abs)
backsubstituteContext vars (Context goal givens zvars) = do
  vars' <- case traverse (\v -> (v,) <$> lookup v zvars) vars of
             Nothing -> Left "backsubstitute: Variables were given that are not zvars"
             Just pairs -> return pairs
  let mp = Map.fromList (map (\(n, e) -> (e, Var n)) vars')
  return $
    Context (replace mp goal)
            (map (second (replace mp)) givens)
            zvars
