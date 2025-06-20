{-# language BangPatterns #-}
{-# language ScopedTypeVariables #-}
{-# language DerivingStrategies #-}
{-# language DuplicateRecordFields #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language MagicHash #-}
{-# language NamedFieldPuns #-}
{-# language UnboxedTuples #-}

-- | Conjunctive normal form
module Arithmetic.Prop.Cnf
  ( Prop(..)
  , Disjunction(..)
  , Conjunction(..)
  , Atom(..)
    -- * Create
  , and
  , true
  , atom
    -- * Convert
  , fromProp
  , toProp
  , toConjunction
    -- * Evaluate
  , implies
    -- * Functions
  , removeRedundantVar
  , simplify
  , map
  , mapM
  ) where

import Prelude hiding (and,map,mapM)

import Control.Applicative (liftA2)
import Data.Primitive (SmallArray)
import Data.Foldable (foldl')
import Arithmetic.Prop (Operator(Eq),Relation(Relation))
import Arithmetic.Expr (Expr)

import qualified Arithmetic.Expr as Expr
import qualified Arithmetic.Prop as E
import qualified Arithmetic.Prop as P
import qualified Arithmetic.Relation as Relation
import qualified Data.List as List
import qualified Data.Primitive as PM
import qualified Data.Primitive.Contiguous as C
import qualified Data.Set as Set
import qualified GHC.Exts as Exts
import qualified Prelude

-- We keep everything sorted so that we can easily do equality
-- tests. If the atom type @v@ is anything remotely interesting,
-- then equality tests can return false negatives but not false
-- positives. That is to say, this is not a substitute for an
-- actual solver. If the atom type @v@ is completely opaque, then
-- equality tests are completely accurate.
--
-- There is another internal representation trick that I should
-- implement but have not yet done. If a disjunctive term subsumes
-- another, we can delete the bigger one. For example:
--
-- > ((a OR b OR c) AND (a OR b))
-- > ===
-- > (a OR b)
--
-- At some point, I just have to go through and figure out where
-- this check needs to be applied.
newtype Prop v = Prop (SmallArray (Disjunction v))
  deriving newtype (Eq)

true :: Prop v
true = Prop mempty

and :: Ord v => Prop v -> Prop v -> Prop v
and (Prop a) (Prop b) = Prop (sortDedupeSmallArray (a <> b))

atom :: v -> Prop v
atom v = Prop (pure (Disjunction (pure v)))

map :: Ord w => (v -> w) -> Prop v -> Prop w
map f (Prop x) = Prop $ sortDedupeSmallArray
  (fmap (\(Disjunction y) -> Disjunction (sortDedupeSmallArray (fmap f y))) x)

mapM :: Ord w => (v -> Maybe w) -> Prop v -> Maybe (Prop w)
mapM f (Prop x) = fmap Prop $ fmap sortDedupeSmallArray
  (traverse (\(Disjunction y) -> fmap Disjunction (fmap sortDedupeSmallArray (traverse f y))) x)

instance Show v => Show (Prop v) where
  showsPrec d (Prop xs) = showParen (d > 10) $
    (\s -> List.intercalate " ∧ " (Prelude.map (\x -> showsPrec 11 x "") (Exts.toList xs)) ++ s)

-- Invariant: Atoms are kept sorted
newtype Disjunction v = Disjunction (SmallArray v)
  deriving newtype (Eq,Ord)

-- Invariant: Atoms are kept sorted
newtype Conjunction v = Conjunction (SmallArray v)
  deriving newtype (Eq,Ord)

instance Show v => Show (Disjunction v) where
  showsPrec d (Disjunction xs) = showParen (d > 10) $
    (\s -> List.intercalate " V " (Prelude.map show (Exts.toList xs)) ++ s)

-- | There are several ways that Atom could be represented. Here,
-- the choice made avoids duplication of the expressions. It also
-- avoids the need for a negation operator.
data Atom v
  = Rel (E.Relation v)
  deriving stock (Eq,Ord)

instance Show v => Show (Atom v) where
  showsPrec d (Rel r) s = showsPrec d r s

sortDedupeSmallArray :: Ord a => SmallArray a -> SmallArray a
sortDedupeSmallArray = Exts.fromList . List.nub . List.sort . Exts.toList

-- ((1 OR 2) AND (3 OR 4 OR 5) AND (...)) OR ((6 OR 7) AND (8 OR 9) AND (...))
disjunction :: Ord v
  => SmallArray (Disjunction v)
  -> SmallArray (Disjunction v)
  -> SmallArray (Disjunction v)
disjunction x y = sortDedupeSmallArray $ do
  a <- x
  applyDisjunction a y

applyDisjunction ::
     Disjunction v
  -> SmallArray (Disjunction v)
  -> SmallArray (Disjunction v)
applyDisjunction (Disjunction d) ys = fmap (\(Disjunction x) -> Disjunction (x <> d)) ys

-- | Convert CNF back to standard representation.
-- TODO: stop calling simplify and then remove Ord constraint
toProp :: Ord v => Prop (Atom v) -> E.Prop v
toProp (Prop xs) = P.simplify $ foldl'
  (\acc (Disjunction ds) -> P.And acc $ foldl'
    (\acc' (Rel r) -> P.Or acc' (P.Rel r)
    ) P.False ds
  ) P.True xs

-- | Returns a conjunction if all conjuncted terms are singleton
-- disjunctions.
toConjunction :: Prop v -> Maybe (Conjunction v)
toConjunction (Prop djs) = fmap Conjunction $ traverse
  (\(Disjunction xs) -> case PM.sizeofSmallArray xs of
    1 -> Just (PM.indexSmallArray xs 0)
    _ -> Nothing
  ) djs

-- | Returns Nothing when the argument expression was False.
fromProp :: Ord v => E.Prop v -> Maybe (Prop (Atom v))
fromProp x0 = case fromPropWorker x0 of
  Nothing -> Nothing
  Just x1 -> Just (Prop (sortDedupeSmallArray x1))

fromPropWorker :: Ord v => E.Prop v -> Maybe (SmallArray (Disjunction (Atom v)))
fromPropWorker x0 = go x0 where
  go :: Ord w => E.Prop w -> Maybe (SmallArray (Disjunction (Atom w)))
  go E.True = Just mempty
  go E.False = Nothing
  go (E.And a b) = liftA2 (<>) (go a) (go b)
  go (E.Or a b) = case go a of
    Nothing -> go b
    Just a' -> case go b of
      Nothing -> Just a'
      Just b' -> Just $! disjunction a' b'
  go (E.Not _) = error "fromExpr: handle Not"
  go (E.Rel x) = Just (pure (Disjunction (pure (Rel x))))

-- | Test if the CNF proposition includes a singleton term with the
-- variable equal to some expression. For example:
--
-- > ((a = b) AND (c = d OR d = 5) AND (z = y + 5))
--
-- The variables a, b, y, and z all have trivial equalities available.
-- (The one for y is considered trivial enough even though it requires
-- some shuffling of terms in the equation).
-- Searching for any one of these causes the equality it is involved
-- in to be removed and the other side of the equality is substituted
-- in everywhere for it.
--
-- This may cause expressions to increase in size, but the total
-- number of expressions decreases by one.
--
-- Food for thought: this could be made more powerful. If we are
-- trying to replace x and encounter a term (x = y OR x = z OR x = ...),
-- then we can use distributivity to replace x with each option
-- in the other terms. This would cause everything else to be
-- duplicated, but it does work, and it's a straightforward extension.
removeRedundantVar :: Ord v => v -> Prop (Atom v) -> Maybe (Prop (Atom v))
removeRedundantVar v p@(Prop xs) = case findEquality v p of
  Nothing -> Nothing
  Just (e,ix) -> Just $! substitute v e (Prop (C.deleteAt xs ix))

-- Return the expression that the variable is equal to and the index
-- into the conjuction array of the term that provided this equality
findEquality :: Ord v => v -> Prop (Atom v) -> Maybe (Expr v, Int)
findEquality v (Prop xs) = C.ifoldr
  (\ix (Disjunction ys) acc -> case PM.sizeofSmallArray ys of
    1 -> case PM.indexSmallArray## ys 0 of
      (# theAtom #) -> case theAtom of
        Rel Relation{left,right,operator} -> case operator of
          Eq | Just (coeff,left') <- Expr.removeVar v left
             , Just left'' <- Expr.divide left' coeff
             , Just right' <- Expr.divide right coeff
               -> Just (Expr.minus right' left'', ix)
             | Just (coeff,right') <- Expr.removeVar v right
             , Just right'' <- Expr.divide right' coeff
             , Just left' <- Expr.divide left coeff
               -> Just (Expr.minus left' right'', ix)
             | otherwise -> acc
          _ -> acc
    _ -> acc
  ) Nothing xs

substitute :: Ord v => v -> Expr v -> Prop (Atom v) -> Prop (Atom v)
substitute v e (Prop xs) = Prop $ C.map'
  (\(Disjunction ys) -> Disjunction $ C.map'
    (\theAtom  -> substituteAtom v e theAtom
    ) ys
  ) xs

substituteAtom :: Ord v => v -> Expr v -> Atom v -> Atom v
substituteAtom v e (Rel r) = Rel (Relation.substitute v e r)

-- Does the first proposition imply the second one.
-- Returns false negatives when atom is nontrivial.
-- Just checks to see if the second argument is a subset of the first.
-- Should be able to get rid of Ord constraint.
implies :: Ord v => Prop v -> Prop v -> Bool
implies (Prop a) (Prop b) = Set.isSubsetOf
  (Set.fromList (Exts.toList b))
  (Set.fromList (Exts.toList a))

-- Simplify a proposition given information about whether or not
-- each atom is trivially true or false. The test for triviality
-- should return:
--
-- * @Just True@ if trivially true
-- * @Just False@ if trivially false
-- * @Nothing@ if atom does not have trivial evaluation
--
-- This function returns Nothing if the resulting proposition is
-- false. CNF has no way to represent this.
simplify :: forall v.
     (v -> Maybe Bool) -- ^ test for trivial
  -> Prop v
  -> Maybe (Prop v)
simplify test (Prop xs) = go 0 [] where
  go :: Int -> [Disjunction v] -> Maybe (Prop v)
  go !ix !acc = if ix < PM.sizeofSmallArray xs
    then
      let v = PM.indexSmallArray xs ix
       in case simplifyDisjunction test v of
            Nothing -> go (ix + 1) acc
            Just ys -> case ys of
              [] -> Nothing
              _ -> go (ix + 1) (Disjunction (Exts.fromList ys) : acc)
    else Just (Prop (Exts.fromList (List.reverse acc)))

-- if this returns Nothing, the whole thing has simplified to true
-- if this return Just [], it is false
simplifyDisjunction :: forall v.
     (v -> Maybe Bool) -- ^ test for trivial
  -> Disjunction v
  -> Maybe [v]
simplifyDisjunction test (Disjunction xs) = go 0 [] where
  go :: Int -> [v] -> Maybe [v]
  go !ix !acc = if ix < PM.sizeofSmallArray xs
    then
      let v = PM.indexSmallArray xs ix
       in case test v of
            Nothing -> go (ix + 1) (v : acc)
            Just True -> Nothing
            Just False -> go (ix + 1) acc
    else Just (List.reverse acc)
