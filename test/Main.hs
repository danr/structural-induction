{-# LANGUAGE TemplateHaskell, Rank2Types #-}
module Main where

import Control.Monad

import System.Exit (exitFailure)

import Test.QuickCheck
import Test.QuickCheck.Test

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

instance Arbitrary TestCase where
    arbitrary = sized $ \ s -> do
        x <- choose (0,2)
        let n = s `div` 30 + x
            m = if n == 0 then 0 else s `div` 30 + x
        tys <- vectorOf n arbitrary
        coords <- vectorOf m (choose (0,n-1))
        return $ TestCase tys coords

    shrink (TestCase tys coords) =
        [ TestCase t (if null t then [] else map (min (length t - 1)) c)
        | t <- shrink tys
        , c <- shrink coords
        ]

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
prop_nat :: SII -> NonNegative Int -> Property
prop_nat sii (NonNegative x) = mkProp sii (natTc x')
  where x' = min 5000 x

-- | Linear, this explodes for lists
prop_maybe :: SII -> NonNegative Int -> NonNegative Int -> Property
prop_maybe sii (NonNegative d) (NonNegative i)
    = mkProp sii (maybeTc (Si Unit) d' i')
  where
    d' = min 100 d
    i' = min 100 i

prop_natnat :: SII -> Property
prop_natnat = flip mkProp (TestCase [Si Nat,Si Nat] [0,1])

prop_tupnatnat :: SII -> Property
prop_tupnatnat = flip mkProp (TestCase [Si (TupTy Nat Nat)] [0,0])

prop_listlist :: SII -> Property
prop_listlist = flip mkProp (TestCase [Si (List (List TyVar))] [0,0])

mkProp :: SII -> TestCase -> Property
mkProp sii tc@(TestCase tys _) =
    forAllShrink (startFromTypes tys) (map shrinkRepr') $ \ start ->
        forAll (makeTracer start parts) $ \ trace ->
            case loop trace of
                Just e  ->
                    printTestCase (show e) $
                    printTestCase (showIndP parts) False
                Nothing -> property True
  where parts = ind sii tc

main :: IO ()
main = do
    let tests = [("structuralInduction",structuralInduction)]
    oks <- forM tests $ \ (name_sii,sii) -> do
        putStrLn $ "== " ++ name_sii ++ " =="
        putStrLn $ "mkProp " ++ name_sii
        ok_big <- quickCheckWithResult stdArgs { maxSuccess = 1000 } (mkProp sii)
        ok_rest <- sequence $(functionExtractorMap "^prop_"
            [| \ name_prop prop -> do
                putStrLn $ name_prop ++ " " ++ name_sii
                quickCheckResult (prop sii) |])
        return $ all isSuccess (ok_big:ok_rest)
    unless (and oks) exitFailure

