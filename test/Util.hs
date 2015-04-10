module Util where

import Test.QuickCheck

halfSize :: (Int -> Gen a) -> Gen a
halfSize m = sized $ \s -> resize (s `div` 2) (m s)

divSize :: Int -> (Int -> Gen a) -> Gen a
divSize d m = sized $ \s -> resize (s `div` d) (m s)

coordss :: Int -> Int -> [[Int]]
coordss n _ | n < 0 = [[]]
coordss 0 d = [replicate d 0]
coordss n d = concat [ map (++ replicate t n) (coordss (n-1) (d-t)) | t <- [0..d] ]

