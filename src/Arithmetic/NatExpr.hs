{-# language BangPatterns #-}
{-# language NamedFieldPuns #-}

-- | This module is a copy of Arithmetic.Expr but with all occurrences
-- of Integer replaced with Natural. Negative coefficients are not allowed.
module Arithmetic.NatExpr
  ( Expr(..)
    -- * Construction
  , var
  , varScaled
  , const
  , plus
    -- * Deconstruction
  , isConst
    -- * Special Expressions
  , zero
    -- * Functions
  , map
  , mentions
  , divide
  , removeVar
  , substitute
  , substituteAll
  , countVars
  , variables
    -- * Compare
  , gte
  , lte
  ) where

import Prelude hiding (const,map)

import Data.Map.Strict (Map)
import Data.String (IsString(..))
import Data.Set (Set)
import Numeric.Natural (Natural)
import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as Merge

-- The Eq instance is accurate.
data Expr v = Expr
  !(Map v Natural)
  -- ^ Variables with multipliers.
  -- Invariant: Cannot use zero as multiplier.
  !Natural
  -- ^ Constant term
  deriving (Eq,Ord)

instance Ord v => Num (Expr v) where
  (+) = plus
  (-) = error "Arithmetic.NatExpr: Num instance does not support subtraction"
  (*) = error "Arithmetic.NatExpr: Num instance does not support multiplication"
  abs = error "Arithmetic.NatExpr: Num instance does not support abs"
  signum = error "Arithmetic.NatExpr: Num instance does not support signum"
  fromInteger i = if i < 0
    then error "Arithmetic.NatExpr: fromIntegral cannot accept negative arg"
    else const (fromIntegral i)

instance Show v => Show (Expr v) where
  showsPrec _ (Expr m x) s = case x of
    0 -> case Map.maxViewWithKey m of
      Just ((k0,v0),m') -> Map.foldrWithKey
        (\k v acc ->
          let acc' = show k ++ " + " ++ acc
           in if v == 1
                then acc'
                else show v ++ " * " ++ acc'
        )
        (let s' = show k0 ++ s
          in if v0 == 1
               then s'
               else show v0 ++ " * " ++ s'
        )
        m'
      Nothing -> showString "0" s
    _ -> Map.foldrWithKey
      (\k v acc ->
        let acc' = show k ++ " + " ++ acc
         in if v == 1
              then acc'
              else show v ++ " * " ++ acc'
      ) (shows x s) m

instance IsString v => IsString (Expr v) where
  fromString s = var (fromString s)

mentions :: Ord v => Expr v -> v -> Bool
mentions (Expr m _) x = Map.member x m

-- | Variable.
var :: v -> Expr v
var x = Expr (Map.singleton x 1) 0

-- | Constant.
const :: Natural -> Expr v
const !x = Expr Map.empty x

-- | Variable multiplied by a constant.
varScaled :: Natural -> v -> Expr v
varScaled s x = case s of
  0 -> zero
  _ -> Expr (Map.singleton x s) 0

multiply :: Natural -> Expr v -> Expr v
multiply !i e@(Expr m c) = case i of
  0 -> zero
  1 -> e
  _ -> Expr (Map.map (\x -> x * i) m) (c * i)

-- | Add two expressions.
plus :: Ord v => Expr v -> Expr v -> Expr v
plus (Expr m0 c0) (Expr m1 c1) = Expr
  ( Merge.merge Merge.preserveMissing Merge.preserveMissing
      (Merge.zipWithMaybeMatched
        (\_ d0 d1 ->
          let d2 = d0 + d1
           in case d2 of
                0 -> Nothing
                _ -> Just d2
        )
      ) m0 m1
  )
  (c0 + c1)

zero :: Expr v
zero = Expr Map.empty 0

isConst :: Expr v -> Maybe Natural
isConst (Expr m x) = case Map.null m of
  True -> Just x
  False -> Nothing

-- | Remove a variable from the term. Returns its coefficient
-- and the rest of the term that the variable has been removed from.
-- Returns Nothing if the variable is not present in the expression.
removeVar :: Ord v => v -> Expr v -> Maybe (Natural, Expr v)
removeVar v (Expr m c) = case Map.updateLookupWithKey (\_ _ -> Nothing) v m of
  (Just coeff, m') -> Just (coeff, Expr m' c)
  (Nothing,_) -> Nothing

-- | Count the total number of variables that appear in the expression.
countVars :: Expr v -> Int
countVars (Expr m _) = Map.size m

-- | List all variables that appear in the expression.
variables :: Expr v -> Set v
variables (Expr m _) = Map.keysSet m

-- | Divide an entire expression by a constant. Returns Nothing
-- if the constant does not divide into all terms evenly.
divide :: Expr v -> Natural -> Maybe (Expr v)
divide (Expr m x) q = liftA2 Expr
  (traverse (\k -> let (c,d) = divMod k q in if d == 0 then Just c else Nothing) m)
  (let (c,d) = divMod x q in if d == 0 then Just c else Nothing)

-- Rename variable to other variables. Use substituteAll to
-- be able to replace variables with expressions as well
map :: Ord w
  => (v -> w)
  -> Expr v -- ^ term @s@ to search in
  -> Expr w -- ^ result, @s@ with occurences of @v@ replaced by @t@
map f (Expr vars coeff) = Expr
  (Map.filter (/= 0) (Map.mapKeysWith (+) f vars))
  coeff

substituteAll :: Ord w
  => (v -> Expr w) -- ^ substitution
  -> Expr v -- ^ term @s@ to search in
  -> Expr w -- ^ result, @s@ with occurences of @v@ replaced by @t@
substituteAll f (Expr vars0 coeff0) = Map.foldlWithKey'
  (\e v coeff -> plus e (multiply coeff (f v))
  ) (const coeff0) vars0

substitute :: Ord v
  => v -- ^ variable @v@
  -> Expr v -- ^ term @t@ to replace variable with
  -> Expr v -- ^ term @s@ to search in
  -> Expr v -- ^ result, @s@ with occurences of @v@ replaced by @t@
substitute v t s = case removeVar v s of
  Nothing -> s
  Just (coeff, s') -> plus (multiply coeff t) s'

-- | Returns true if all variable instantiations cause the first term
-- to be greater than the second term.
--
-- Note: This does not agree with the 'Ord' instance for this type.
gte :: Ord v => Expr v -> Expr v -> Bool
gte (Expr coeffs1 const1) (Expr coeffs2 const2)
  | const2 > const1 = False
  | otherwise =
      let m = Merge.mergeA
            Merge.dropMissing (Merge.traverseMissing (\_ _ -> Nothing))
            (Merge.zipWithAMatched (\_ x y -> if x >= y then Just x else Nothing))
            coeffs1 coeffs2
       in case m of
            Nothing -> False
            Just _ -> True

-- | See documentation for 'gte'.
lte :: Ord v => Expr v -> Expr v -> Bool
lte (Expr coeffs1 const1) (Expr coeffs2 const2)
  | const1 > const2 = False
  | otherwise =
      let m = Merge.mergeA
            (Merge.traverseMissing (\_ _ -> Nothing)) Merge.dropMissing 
            (Merge.zipWithAMatched (\_ x y -> if x <= y then Just y else Nothing))
            coeffs1 coeffs2
       in case m of
            Nothing -> False
            Just _ -> True
