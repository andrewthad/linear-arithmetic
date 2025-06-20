{-# language BangPatterns #-}
{-# language ScopedTypeVariables #-}
{-# language DerivingStrategies #-}
{-# language DuplicateRecordFields #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language MagicHash #-}
{-# language NamedFieldPuns #-}
{-# language UnboxedTuples #-}

-- | Conjunction of atoms
module Arithmetic.Prop.Conjunction
  ( Conjunction(..)
  , and
  , atom
  ) where

import Prelude hiding (and)

import Arithmetic.Prop.Cnf (Conjunction(..))
import Data.Primitive (SmallArray)

import qualified Data.List as List
import qualified GHC.Exts as Exts

and :: Ord v => Conjunction v -> Conjunction v -> Conjunction v
and (Conjunction a) (Conjunction b) =
  Conjunction (sortDedupeSmallArray (a <> b))

atom :: v -> Conjunction v
atom v = Conjunction (pure v)

sortDedupeSmallArray :: Ord a => SmallArray a -> SmallArray a
sortDedupeSmallArray = Exts.fromList . List.nub . List.sort . Exts.toList
