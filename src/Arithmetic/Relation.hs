{-# language DeriveFunctor #-}
{-# language DuplicateRecordFields #-}
{-# language NamedFieldPuns #-}
{-# language ScopedTypeVariables #-}

module Arithmetic.Relation
  ( Relation(..)
  , Operator(..)
    -- * Functions
  , substitute
  , substituteAll
  , map
  ) where

import Prelude hiding (map)

import Arithmetic.Expr (Expr)
import qualified Arithmetic.Expr as Expr

-- Note: the Eq instance returns false negatives. 
data Relation v = Relation
  { operator :: Operator
  , left :: Expr v
  , right :: Expr v
  } deriving (Eq,Ord)

map :: Ord w => (v -> w) -> Relation v -> Relation w
map f Relation{operator,left,right} = Relation
  { operator
  , left = Expr.map f left
  , right = Expr.map f right
  }

substituteAll :: Ord w => (v -> Expr w) -> Relation v -> Relation w
substituteAll f Relation{operator,left,right} = Relation
  { operator
  , left = Expr.substituteAll f left
  , right = Expr.substituteAll f right
  }

data Operator
  = Eq
  | Neq
  | Lt
  | Lte -- should probably get rid of Lte
  deriving (Show,Eq,Ord)

instance Show v => Show (Relation v) where
  showsPrec d Relation{left,operator,right} = showParen (d > 10) $
    showsPrec 0 left .
    showsOpWithSpace operator .
    showsPrec 0 right

-- internal function
showsOpWithSpace :: Operator -> String -> String
showsOpWithSpace op s = case op of
  Eq -> ' ' : '=' : ' ' : s
  Neq -> ' ' : '≠' : ' ' : s
  Lt -> ' ' : '<' : ' ' : s
  Lte -> ' ' : '≤' : ' ' : s

-- | TODO: consider checking first to improve sharing
substitute :: Ord v => v -> Expr v -> Relation v -> Relation v
substitute v e Relation{left,right,operator} = Relation
  { left = Expr.substitute v e left
  , right = Expr.substitute v e right
  , operator
  }
