{-# LANGUAGE TemplateHaskell #-}

module Test.Data.Tree.Optic (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Tree.Optic
import Data.Tree
import Data.Profunctor.Optic

tests :: IO Bool
tests = checkParallel $$(discover)

genTree :: Gen (Tree Int)
genTree = Gen.recursive Gen.choice
    [Node <$> Gen.int (Range.linear 0 100) <*> pure []]
    [Node <$> Gen.int (Range.linear 0 100) <*> Gen.list (Range.linear 1 3) genTree]

-- root: get/set roundtrip
prop_root_getset :: Property
prop_root_getset = property $ do
    t <- forAll genTree
    view root t === rootLabel t

prop_root_setget :: Property
prop_root_setget = property $ do
    t <- forAll genTree
    v <- forAll $ Gen.int (Range.linear 0 100)
    view root (set root v t) === v

-- branches: get/set roundtrip
prop_branches_getset :: Property
prop_branches_getset = property $ do
    t <- forAll genTree
    view branches t === subForest t

prop_branches_setget :: Property
prop_branches_setget = property $ do
    t <- forAll genTree
    let bs = view branches t
    set branches bs t === t
