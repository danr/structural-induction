{-# OPTIONS_GHC -fno-warn-missing-methods #-}
{-# LANGUAGE ViewPatterns #-}
module Nat where

import Test.QuickCheck

-- A classic!
data Nat = Z | S Nat deriving (Show,Eq)

instance Arbitrary Nat where
    arbitrary = sized $ \ s -> do
        x <- choose (0,round (sqrt (toEnum s) :: Double))
        return (nats !! x)

    shrink (S n) = n : shrink n
    shrink Z     = []

nats :: [Nat]
nats = iterate S Z

-- warning: partial instance
instance Num Nat where
    fromInteger n = nats !! fromEnum n

-- Another classic!
data PInt
    = P { p :: Nat }
    | N { p :: Nat }
  deriving (Show,Eq)

instance Arbitrary PInt where
    arbitrary = do
        (b,x) <- arbitrary
        return $ if b then P x else N x

    shrink (p -> n ) = map P (shrink n) ++ map N (shrink n)

-- warning: partial instance
instance Num PInt where
    fromInteger x
        | x < 0     = N (fromInteger (negate (x + 1)))
        | otherwise = P (fromInteger x)

