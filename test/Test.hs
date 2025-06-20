{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeApplications #-}

import Test.Tasty (TestTree,defaultMain,testGroup)
import Test.Tasty.HUnit (testCase,(@=?))

import qualified Arithmetic.Prop.Cnf as Cnf
import qualified Arithmetic.Prop.Conjunction as Conjunction
import qualified Arithmetic.Relation.Idl as Idl
import qualified GHC.Exts as Exts

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "idl-sat"
  [ testCase "a" $
      False
      @=?
      Idl.satisfiable
      ( Conjunction.atom Idl.Relation{alpha="a",beta="b",constant=(-5)}
        `Conjunction.and`
        Conjunction.atom Idl.Relation{alpha="b",beta="a",constant=(-3)}
      )
  , testCase "b" $
      True
      @=?
      Idl.satisfiable
      ( Conjunction.atom Idl.Relation{alpha="a",beta="b",constant=(-5)}
        `Conjunction.and`
        Conjunction.atom Idl.Relation{alpha="b",beta="c",constant=(-5)}
        `Conjunction.and`
        Conjunction.atom Idl.Relation{alpha="a",beta="c",constant=(-20)}
      )
  , testCase "c" $
      False
      @=?
      Idl.satisfiable
      ( Conjunction.atom Idl.Relation{alpha="x1",beta="x3",constant=(-6)}
        `Conjunction.and`
        Conjunction.atom Idl.Relation{alpha="x2",beta="x1",constant=(-3)}
        `Conjunction.and`
        Conjunction.atom Idl.Relation{alpha="x2",beta="x1",constant=3}
        `Conjunction.and`
        Conjunction.atom Idl.Relation{alpha="x3",beta="x2",constant=2}
        `Conjunction.and`
        Conjunction.atom Idl.Relation{alpha="x3",beta="x4",constant=(-1)}
        `Conjunction.and`
        Conjunction.atom Idl.Relation{alpha="x4",beta="x2",constant=5}
      )
  , testCase "d" $
      True
      @=?
      Idl.satisfiable
      ( Conjunction.atom Idl.Relation{alpha="x1",beta="x3",constant=(-5)}
        `Conjunction.and`
        Conjunction.atom Idl.Relation{alpha="x1",beta="x4",constant=(-3)}
        `Conjunction.and`
        Conjunction.atom Idl.Relation{alpha="x2",beta="x1",constant=3}
        `Conjunction.and`
        Conjunction.atom Idl.Relation{alpha="x3",beta="x2",constant=2}
        `Conjunction.and`
        Conjunction.atom Idl.Relation{alpha="x3",beta="x4",constant=(-1)}
        `Conjunction.and`
        Conjunction.atom Idl.Relation{alpha="x4",beta="x2",constant=5}
      )
  ]
