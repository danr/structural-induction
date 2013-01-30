{-# LANGUAGE TemplateHaskell, Rank2Types #-}
module Main where

import Control.Monad

import System.Exit (exitFailure)

import Test.QuickCheck
import Test.QuickCheck.Test
import Test.Feat.Access
import Test.Feat.Modifiers (nat)

import Language.Haskell.Extract

import Induction.Structural

import Trace
import Env
import EnvTypes
import Walk

-- | Structural Induction Instatiator
type SII = TyEnv Con' Ty' -> [(String,Ty')] -> [Int] -> [IndPartV Con' String Ty']

-- | Do induction on a test case
ind :: SII -> TestCase -> [IndP]
ind sii (TestCase types coords) =
    map (unV (\ x i -> x ++ show i)) $ sii testEnv' args coords
  where
    args = zip vars types

    vars :: [String]
    vars = concat [ replicateM n ['a'..'z'] | n <- [1..] ]

data TestCase = TestCase [Ty'] [Int]
  deriving Show

unitTc :: Int -> [Int] -> TestCase
unitTc n = TestCase (replicate n (Si Unit))

boolTc :: Int -> [Int] -> TestCase
boolTc x = TestCase (replicate x (Si Bool))

natTc :: Int -> TestCase
natTc x = TestCase [Si Nat] (replicate x 0)

maybeTc :: Ty' -> Int -> Int -> TestCase
maybeTc t d i = TestCase [repeatMaybe t d] (replicate i 0)

repeatMaybe :: Ty' -> Int -> Ty'
repeatMaybe t = go
  where
    go n | n <= 0    = t
         | otherwise = case go (n - 1) of Si t' -> Si (Maybe t')

mods :: Int -> [Int] -> [Int]
mods 0 _  = []
mods x xs = map (`mod` x) xs

-- | Linear
prop_units :: SII -> NonNegative Int -> [Int] -> Property
prop_units sii (NonNegative x) xs
    = mkProp sii (unitTc x' (mods x' xs))
  where x' = min 5000 x

-- | Can't try this too far because of exponential explosion
prop_bools :: SII -> NonNegative Int -> [Int] -> Property
prop_bools sii (NonNegative x) xs
    = mkProp sii (boolTc x' (mods x' xs))
  where x' = min 10 x

-- | Linear
prop_maybe :: SII -> NonNegative Int -> NonNegative Int -> Property
prop_maybe sii (NonNegative d) (NonNegative i)
    = mkProp sii (maybeTc (Si Unit) d' i')
  where
    d' = min 100 d
    i' = min 100 i

mkPropTy :: SII -> Ty' -> Int -> Property
mkPropTy sii ty n = mkProp sii (TestCase [ty] (replicate n 0))

mkProp :: SII -> TestCase -> Property
mkProp sii tc@(TestCase tys _) =
    forAllShrink (startFromTypes tys) (mapM shrinkRepr') $ \ start ->
        forAll (makeTracer start parts) $ \ trace ->
            case loop trace of
                Just e  ->
                    printTestCase (show e) $
                    printTestCase (showIndP parts) False
                Nothing -> property True
  where parts = ind sii tc

tryWithTypes :: SII -> [Ty'] -> [Int] -> Property
tryWithTypes sii = (mkProp sii .) . TestCase

coordss :: [[Int]]
coordss = [ replicate (d - r) 0 ++ replicate r 1 | d <- [0..4], r <- [0..d] ]

main :: IO ()
main = do
    let tests =
            [("subtermInduction",subtermInduction)
            ,("caseAnalysis",caseAnalysis)
            -- ,("structuralInductionUnsound",structuralInductionUnsound)
            ]
    oks <- forM tests $ \ (name_sii,sii) -> do
        putStrLn $ "== " ++ name_sii ++ " =="

        ok_feat <- forM [0..500] $ \ ix -> forM [1..4] $ \ d -> do
            let ty = indexWith enumTy' ix
                size = 100 `div` d
            putStrLn $ name_sii ++ ": " ++ show ty ++ " depth: " ++ show d
            quickCheckWithResult stdArgs { maxSize = size } (mkPropTy sii ty d)


        ok_dbl_feat <- forM [0..500] $ \ ix -> forM coordss $ \ coords -> do
            let (i,j) = index ix
                ty1 = indexWith enumTy' (nat i)
                ty2 = indexWith enumTy' (nat j)
                tys = [ty1,ty2]
                size = 100 `div` length coords
            putStrLn $ name_sii ++ ": " ++ show tys ++ " coords: " ++ show coords
            quickCheckWithResult stdArgs { maxSize = size } (tryWithTypes sii tys coords)


        ok_manual <- sequence $(functionExtractorMap "^prop_"
            [| \ name_prop prop -> do
                putStrLn $ name_sii ++ ": " ++ name_prop
                quickCheckResult (prop sii) |])

        return $ all isSuccess (ok_manual ++ concat (ok_feat ++ ok_dbl_feat))

    unless (and oks) exitFailure

