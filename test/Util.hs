module Util where

import Test.QuickCheck

halfSize :: (Int -> Gen a) -> Gen a
halfSize m = sized $ \s -> resize (s `div` 2) (m s)

