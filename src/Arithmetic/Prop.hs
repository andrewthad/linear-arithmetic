{-# language DuplicateRecordFields #-}
{-# language NamedFieldPuns #-}
{-# language ScopedTypeVariables #-}

module Arithmetic.Prop
  ( Prop(..)
  , Relation(..)
  , Operator(..)
  , Expr
    -- * Functions
  , member
  , simplify
  , rename
  , substitute
  , removeUnrelatedVar
  , variables
    -- * Builders
  , (<.)
  , (=.)
  ) where

import Prelude hiding (Bool(True,False))
import Control.Applicative (liftA2)
import Data.Int (Int64)
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Arithmetic.Expr (Expr)
import Arithmetic.Relation (Relation(..),Operator(..))

import qualified Prelude as P
import qualified Data.Set as Set
import qualified Arithmetic.Expr as E
import qualified Arithmetic.Expr as Expr

-- | Paremeterized by the name for a term. Numbers and strings
-- are common choices. These terms are quantifier-free.
data Prop v
  = True
  | False
  | And (Prop v) (Prop v)
  | Or (Prop v) (Prop v)
  | Not (Prop v)
  | Rel (Relation v)
  deriving (Show)

(<.) :: Expr v -> Expr v -> Prop v
(<.) a b = Rel Relation{operator=Lt,left=a,right=b}

(=.) :: Expr v -> Expr v -> Prop v
(=.) a b = Rel Relation{operator=Eq,left=a,right=b}

-- | Does the variable appear in the proposition?
member :: Ord v => v -> Prop v -> P.Bool
member v p0 = go p0 where
  go True = P.False
  go False = P.False
  go (And x y) = go x || go y
  go (Or x y) = go x || go y
  go (Not x) = go x
  go (Rel Relation{left,right}) = E.mentions left v || E.mentions right v

variables :: Ord v => Prop v -> Set v
variables p0 = go p0 where
  go True = Set.empty
  go False = Set.empty
  go (And x y) = go x <> go y
  go (Or x y) = go x <> go y
  go (Not x) = go x
  go (Rel Relation{left,right}) = E.variables left <> E.variables right

-- | Remove this variable if it is not constrained in any way that
-- interacts with other variables. That is, if it is only related to
-- constants, then these propositions are replaced by Truth. This
-- also succeds if the variable does not appear.
--
-- If the variable is related to itself in an unsatisfiable way
-- (e.g. @x = x + 2@) this replaces that proposition with False.
-- If the variable appears in more than one proposition, this
-- currently returns Nothing. It should be possible to correct
-- this behavior. We need to test satisfiability in that case.
-- If we have something like (x < 7) AND (x > 7), then this should
-- be able to replace that with False, but it cannot do that at
-- the moment.
removeUnrelatedVar :: Ord v => v -> Prop v -> Maybe (Prop v)
removeUnrelatedVar v p0 = case findSoleOccurence v p0 of
  ReplaceWithTrue -> Just (replaceSoleOccurence v True p0)
  ReplaceWithFalse -> Just (replaceSoleOccurence v False p0)
  CannotReplace -> Nothing
  NotFound -> Just p0

data SoleOccurenceResult
  = NotFound
  | CannotReplace
  | ReplaceWithTrue
  | ReplaceWithFalse

-- Internal function. If the variable only shows up in one
-- place, and the relation does not include any other variables,
-- returns Just. Otherwise, returns Nothing. The Bool inside the
-- result is whether or not the relation was satisfiable.
findSoleOccurence :: Ord v => v -> Prop v -> SoleOccurenceResult
findSoleOccurence v p0 = go p0
  where
  go True = NotFound
  go False = NotFound
  go (And x y) =
    let mx = go x
        my = go y
     in case mx of
          NotFound -> my
          _ -> case my of
            NotFound -> my
            _ -> CannotReplace
  go (Or x y) =
    let mx = go x
        my = go y
     in case mx of
          NotFound -> my
          _ -> case my of
            NotFound -> my
            _ -> CannotReplace
  go (Not x) = go x
  go (Rel Relation{operator,left,right}) = case E.removeVar v left of
    Nothing -> case E.removeVar v right of
      Nothing -> NotFound
      Just (rightCoeff,right')
        | Just leftConst <- E.isConst left
        , Just rightConst <- E.isConst right'
          -- Equation is of form: leftConst ?= rightCoeff * x + rightConst
          -- Any operator has a trivial solution except for equality.
          -> case operator of
            Eq -> if rem (leftConst - rightConst) rightCoeff == 0
              then ReplaceWithTrue
              else ReplaceWithFalse
            _ -> ReplaceWithTrue
        | otherwise -> CannotReplace
    Just (leftCoeff,left') -> case E.removeVar v right of
      Nothing
        | Just leftConst <- E.isConst left'
        , Just rightConst <- E.isConst right
          -- Equation is of form: leftCoeff * x + leftConst ?= rightConst
          -- Any operator has a trivial solution except for equality.
          -> case operator of
            Eq -> if rem (rightConst - leftConst) leftCoeff == 0
              then ReplaceWithTrue
              else ReplaceWithFalse
            _ -> ReplaceWithTrue
        | otherwise -> CannotReplace
      Just (rightCoeff,right')
        | Just leftConst <- E.isConst left'
        , Just rightConst <- E.isConst right'
          -> case operator of
            -- 2x + 2 = 3x solved by x = 2
            -- 2x = 3x solved by x = 0
            -- 4x + 1 = 7x has no solution
            Eq ->
              let deltaConst = abs (leftConst - rightConst)
                  deltaCoeff = abs (leftCoeff - rightCoeff)
               in if deltaCoeff == 0
                    then if deltaConst == 0
                      then ReplaceWithTrue
                      else ReplaceWithFalse
                    else if rem deltaConst deltaCoeff == 0
                      then ReplaceWithTrue
                      else ReplaceWithFalse
            Neq ->
              let deltaConst = abs (leftConst - rightConst)
                  deltaCoeff = abs (leftCoeff - rightCoeff)
               in if deltaCoeff == 0
                    then if deltaConst == 0
                      then ReplaceWithFalse
                      else ReplaceWithTrue
                    else ReplaceWithTrue
            _ -> error "Arithmetic.Prop: write the cases for LT and LTE"
        | otherwise -> CannotReplace


-- Internal function.
-- Precondition: variable must only occur once in the entire proposition.
replaceSoleOccurence :: Ord v => v -> Prop v -> Prop v -> Prop v
replaceSoleOccurence v w p0 = go p0
  where
  go True = True
  go False = False
  go (And x y) = And (go x) (go y)
  go (Or x y) = Or (go x) (go y)
  go (Not x) = Not (go x)
  go p@(Rel Relation{left,right}) = if E.mentions left v || E.mentions right v
    then w
    else p

-- | Rename all occurences of variable @v@ with @w@. The variable @w@
-- must not occur in the proposition already. Throws an exception if
-- it does.
rename :: Ord v => v -> v -> Prop v -> Prop v
rename v w p0 = if member w p0
  then error "Arithmetic.Prop.rename: new name already exists"
  else go p0
  where
  go True = True
  go False = False
  go (And x y) = And (go x) (go y)
  go (Or x y) = Or (go x) (go y)
  go (Not x) = Not (go x)
  go (Rel Relation{operator,left,right}) = Rel Relation
    { left=Expr.substitute v (Expr.var w) left
    , right=Expr.substitute v (Expr.var w) right
    , operator
    }

-- | Replace all occurences of @v@ with the expression.
substitute :: Ord v => v -> Expr v -> Prop v -> Prop v
substitute v w p0 = go p0
  where
  go True = True
  go False = False
  go (And x y) = And (go x) (go y)
  go (Or x y) = Or (go x) (go y)
  go (Not x) = Not (go x)
  go (Rel Relation{operator,left,right}) = Rel Relation
    { left=Expr.substitute v w left
    , right=Expr.substitute v w right
    , operator
    }

-- | Performs the following substitutions:
--
-- * @a = a  ==>  True@
-- * @a ≠ a  ==>  False@
-- * @p ∧ T  ==>  p@ (and symmetric variant)
-- * @p ∧ F  ==>  F@ (and symmetric variant)
-- * @p V T  ==>  T@ (and symmetric variant)
-- * @p V F  ==>  p@ (and symmetric variant)
--
-- Also, if both sides of a relation are constants, replaces
-- the expression with the result.
--
-- TODO: Add some simplifications of relations. In particular,
-- expressions like @2x + 1 = x + 0@ should become @x + 1 = 0@.
simplify :: forall v. Ord v => Prop v -> Prop v
simplify = go where
  go :: Prop v -> Prop v
  go True = True
  go False = False
  go (And x y) = case go x of
    True -> go y
    False -> False
    x' -> case go y of
      True -> x'
      False -> False
      y' -> And x' y'
  go (Or x y) = case go x of
    True -> True
    False -> go y
    x' -> case go y of
      True -> True
      False -> x'
      y' -> Or x' y'
  go (Not x) = go x
  go r@(Rel Relation{operator,left,right}) = case operator of
    Eq -> if left == right then True else r
    Neq -> if left == right then False else r
    Lt -> fromMaybe r $ do
      a <- E.isConst left
      b <- E.isConst right
      Just (if a < b then True else False)
    Lte -> fromMaybe r $ do
      a <- E.isConst left
      b <- E.isConst right
      Just (if a <= b then True else False)
