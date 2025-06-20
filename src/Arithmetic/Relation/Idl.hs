{-# language BangPatterns #-}
{-# language NamedFieldPuns #-}
{-# language ScopedTypeVariables #-}

module Arithmetic.Relation.Idl
  ( Relation(..)
  , satisfiable
  , complement
  ) where

import Arithmetic.Prop.Cnf (Conjunction(Conjunction))
import Data.Map.Strict (Map)
import Control.Monad.ST (runST)
import Data.Foldable (for_,foldl')
import Control.Monad (replicateM_,when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT(MaybeT),runMaybeT)

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Primitive as PM

-- The relation modeled is:
--
-- > alpha <= beta + constant
--
-- Invariant: beta and alpha must be different
data Relation v = Relation
  { alpha :: !v
  , beta :: !v
  , constant :: !Integer
  } deriving (Eq,Ord)

-- complement (a <= b + K)
-- ==> a > b + K
-- ==> a >= b + K - 1
-- ==> -a <= -b - K + 1
-- ==> b <= a + (-K + 1)
complement :: Relation v -> Relation v 
complement Relation{alpha,beta,constant} = Relation
  { alpha = beta
  , beta = alpha
  , constant = negate constant + 1
  }

-- Completely accurate
satisfiable :: (Show v, Ord v) => Conjunction (Relation v) -> Bool
satisfiable (Conjunction rels)
  | PM.sizeofSmallArray rels == 0 = True
  | otherwise =
      let allVars = foldMap
            (\Relation{alpha,beta} ->
              Set.singleton alpha <> Set.singleton beta
            ) rels
          assignments = foldl'
            (\acc (ix :: Int, v) -> Map.insert v ix acc
            ) Map.empty (zip [0..] (Set.toList allVars))
          rawSize = Set.size allVars
          root = rawSize
          size = rawSize + 1
          -- All variables in rels' are densely packed integers
          -- The index of the magic root node (for bellman ford) is size
          rels' = fmap (substitute assignments) rels
       in runST $ do
            distMut <- PM.newSmallArray (size * size) (Nothing :: Maybe Integer)
            shortestPaths0 <- PM.newSmallArray size Nothing
            let initRoot !node = if node < size
                  then do
                    PM.writeSmallArray distMut (root * size + node) (Just 0)
                    PM.writeSmallArray shortestPaths0 node (Just (Distance 0 0))
                    initRoot (node + 1)
                  else pure ()
            initRoot 0
            for_ rels' $ \Relation{alpha,beta,constant} -> 
              PM.writeSmallArray distMut (alpha * size + beta) (Just constant)
            graph <- PM.unsafeFreezeSmallArray distMut
            let once !shortestPaths = do
                  let goA !src = case src of
                        (-1) -> pure ()
                        _ -> do
                          let goB !dst = case dst of
                                (-1) -> pure ()
                                _ -> do
                                  _ <- runMaybeT $ do
                                    edge <- MaybeT (pure (PM.indexSmallArray graph (src * size + dst)))
                                    Distance _ srcDist <- MaybeT (PM.readSmallArray shortestPaths src)
                                    mdst <- lift (PM.readSmallArray shortestPaths dst)
                                    case mdst of
                                      Nothing -> do
                                        lift (PM.writeSmallArray shortestPaths dst (Just (Distance src (srcDist + edge))))
                                      Just (Distance _ dstDist) -> do
                                        when (srcDist + edge < dstDist) $ do
                                          lift (PM.writeSmallArray shortestPaths dst (Just (Distance src (srcDist + edge))))
                                  goB (dst - 1)
                          goB (size - 1)
                          goA (src - 1)
                  goA (size - 1)
            replicateM_ size (once shortestPaths0)
            shortestPathsA <- PM.freezeSmallArray shortestPaths0 0 size
            once shortestPaths0
            shortestPathsB <- PM.unsafeFreezeSmallArray shortestPaths0
            -- error (show shortestPathsA ++ "\n\n" ++ show shortestPathsB)
            pure (shortestPathsA == shortestPathsB)

data Distance = Distance
  !Int -- parent
  !Integer -- distance from root
  deriving (Eq,Show)

-- crashes when v missing from map
substitute :: Ord v => Map v w -> Relation v -> Relation w
substitute m Relation{alpha,beta,constant} = Relation
  { alpha = case Map.lookup alpha m of
      Just x -> x
      Nothing -> error "Arithmetic.Relation.Idl.substitute: mistake"
  , beta = case Map.lookup beta m of
      Just x -> x
      Nothing -> error "Arithmetic.Relation.Idl.substitute: mistake"
  , constant = constant
  }
