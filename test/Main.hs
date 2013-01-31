{-# LANGUAGE TemplateHaskell, Rank2Types #-}
module Main where

import Control.Monad
import Control.Applicative

import Data.List
import Data.Ord

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
import Util

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
                Just e  -> printTestCase (showIndP parts) False
                Nothing -> property True
  where parts = ind sii tc

makeTestCases :: Integer -> IO [TestCase]
makeTestCases tests = concat <$>
    forM [0..tests] (\ ix -> do
        let tys = indexWith enumTy's ix
            all_coordss = concat [ coordss (length tys - 1) d | d <- [0..4] ]
        coordss' <- head <$> sample' (shuffle all_coordss)
        let css = nub . sortBy (comparing length) . sort . take 20 $ coordss'
        return $ map (TestCase tys) css
    )

main :: IO ()
main = do
    let tests =
            [("subtermInductionQ",subtermInductionQ)
            ,("subtermInduction",subtermInduction)
            ,("caseAnalysis",caseAnalysis)
            ]
            -- [("structuralInductionUnsound",structuralInductionUnsound)]
    oks <- forM tests $ \ (name_sii,sii) -> do
        putStrLn $ "== " ++ name_sii ++ " =="

        testcases <- makeTestCases 500
        let tests = length testcases

        ok_feat <- forM (zip testcases [0..]) $ \ (tc@(TestCase tys cs),i) -> do
            putStrLn $ "(" ++ show i ++ "/" ++ show tests ++ ") " ++
                       name_sii ++ ": " ++ show tys ++ " coords: " ++ show cs
            quickCheckResult (mkProp sii tc)

        ok_manual <- sequence $(functionExtractorMap "^prop_"
            [| \ name_prop prop -> do
                putStrLn $ name_sii ++ ": " ++ name_prop
                quickCheckResult (prop sii) |])

        return $ all isSuccess (ok_manual ++ ok_feat)

    unless (and oks) exitFailure

