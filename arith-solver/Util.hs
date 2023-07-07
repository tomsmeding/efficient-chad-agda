{-# LANGUAGE TupleSections #-}
module Util where

import Data.Foldable
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Bifunctor (first)
import Data.Maybe (fromMaybe)


substitute :: Eq a => a -> a -> [a] -> [a]
substitute _ _ [] = []
substitute a b (c:cs) | a == c = b : substitute a b cs
                      | otherwise = c : substitute a b cs

firstF :: Functor f => (a -> f b) -> (a, c) -> f (b, c)
firstF f (x, y) = (,y) <$> f x

secondF :: Functor f => (b -> f c) -> (a, b) -> f (a, c)
secondF f (x, y) = (x,) <$> f y

implicitGraph :: (Foldable t, Ord k) => (k -> t k) -> [k] -> Map k [k]
implicitGraph nexts nodes =
  let nodes' = toList $ foldMap (Set.fromList . toList . nexts) nodes
  in Map.fromList (map (\k -> (k, toList (nexts k))) nodes')

oppositeGraph :: Ord k => Map k [k] -> Map k [k]
oppositeGraph =
  Map.fromListWith (++)
  . concatMap (\(k, vs) -> map (,[k]) vs)
  . Map.assocs

-- | Returns Nothing if the graph contains cycles. Slow algorithm, but is
-- stable: whenever possible, returns a nodes in the order given.
topSort :: (Foldable t, Ord k) => (a -> k) -> (a -> t k) -> [a] -> Maybe [a]
topSort = \keyOfNode dependenciesOfKey nodes ->
  let nodeMap = Map.fromList (map (\n -> (keyOfNode n, n)) nodes)
      -- keys = Map.keysSet nodeMap
      deps = Map.map (Set.fromList . toList . dependenciesOfKey) nodeMap
      -- keyOrder = topSort' keys deps
      kaas = topSort2 (map keyOfNode nodes) deps
  in map (nodeMap Map.!) <$> kaas
  where
    topSort2 ::  Ord addr => [addr] -> Map addr (Set addr) -> Maybe [addr]
    topSort2 addrs mp =
      let nincoming0 = Map.fromListWith (+) [(suc, 1::Int) | n <- addrs, suc <- maybe [] toList (Map.lookup n mp)]
          loop list inc = case whittle list inc of
                            Left (n, list', inc') -> (n :) <$> loop list' inc'
                            Right True -> Just []
                            Right False -> Nothing
      in loop addrs nincoming0
      where
        -- Returns Left on producing an element of the topsort; continue the loop.
        -- Returns Right upon completion: Right True if we're done, Right False if a loop was detected.
        whittle [] _ = Right True
        whittle (n : ns) inc =
          case Map.lookup n inc of
            Just count | count > 0 ->
              first (\(node, list', inc') -> (node, n : list', inc'))
                    (whittle ns inc)
            _ ->
              let sucs = maybe [] toList (Map.lookup n mp)
                  inc' = foldr (Map.adjust (subtract 1)) inc sucs
              in Left (n, ns, inc')

-- | Returns Nothing if the graph contains cycles.
topSortOpposite :: (Foldable t, Ord k) => (a -> k) -> (a -> t k) -> [a] -> Maybe [a]
topSortOpposite keyOfNode dependenciesOfKey nodes =
  let graph1 = Map.fromList $ map (\x -> (keyOfNode x, toList (dependenciesOfKey x))) nodes
      graph2 = oppositeGraph graph1
  in topSort keyOfNode (fromMaybe [] . (`Map.lookup` graph2) . keyOfNode) nodes
