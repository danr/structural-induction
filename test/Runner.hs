{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import Control.Monad (unless)
import Control.Applicative

import System.Exit (exitFailure)

import Test.QuickCheck
import Test.QuickCheck.All

import Induction.Structural

import Trace
import Env
import EnvTypes
import Walk

-- | Do induction on a test case
ind :: TestCase -> [IndP]
ind (TestCase types coords) = map (unV (\ x i -> x ++ show i)) $
    structuralInduction testEnv' args coords
  where
    args = zip (map return ['a'..'z']) types

data TestCase = TestCase [Ty'] [Int]
  deriving Show

instance Arbitrary TestCase where
    arbitrary = sized $ \ s -> resize (s `div` 3) $ do
        tys <- take 5 <$> arbitrary
        let n = length tys
        coords <- take 5 <$> case n of
            0 -> return []
            _ -> listOf (choose (0,n-1))
        return $ TestCase tys coords

    shrink (TestCase tys coords) =
        [ TestCase t (if null t then [] else map (min (length t - 1)) c)
        | t <- shrink tys
        , c <- shrink coords
        ]

natTc :: Int -> TestCase
natTc x = TestCase [Si Nat] (replicate (min 1000 x) 0)

prop_nat :: NonNegative Int -> Property
prop_nat (NonNegative x) = prop_mkProp (natTc x)

prop_natnat :: Property
prop_natnat = prop_mkProp (TestCase [Si Nat,Si Nat] [0,1])

prop_tupnatnat :: Property
prop_tupnatnat = prop_mkProp (TestCase [Si (TupTy Nat Nat)] [0,0])

prop_listlist :: Property
prop_listlist = prop_mkProp (TestCase [Si (List (List TyVar))] [0,0])

prop_mkProp :: TestCase -> Property
prop_mkProp tc@(TestCase tys _) =
    let parts = ind tc
    in  forAll (startFromTypes tys) $ \ start ->
            forAll (makeTracer start parts) $ \ trace ->
                case loop trace of
                    Just e  ->
                        printTestCase (show e) $
                        printTestCase (showIndP parts) False
                    Nothing -> property True

boolTc :: Int -> TestCase
boolTc x = TestCase (replicate x (Si Bool)) [0..x-1]

-- This fails with n > 26?!!

prop_bools :: NonNegative Int -> Property
prop_bools (NonNegative x) = prop_mkProp (boolTc x)

main = do
    ok <- $quickCheckAll
    unless ok exitFailure
