{-# OPTIONS_HADDOCK hide #-}
-- | Internal auxiliary functions (pertaining to general haskell types)
module Induction.Structural.Auxiliary where

import Control.Monad (liftM)
import Data.List     (sortBy, groupBy)
import Data.Function (on)
import Data.Ord      (comparing)

-- | Concatenate the results after mapM
concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = liftM concat . mapM f

infixr 9 .:

-- | Function composition deluxe
--
--   @(f .: g) = \x y -> f (g x y)@
(.:) :: (b -> c) -> (a -> a' -> b) -> a -> a' -> c
(.:) = (.) . (.)

-- | /O(n log n)/ group, but destroys ordering
groupSortedOn :: Ord b => (a -> b) -> [a] -> [[a]]
groupSortedOn f = groupBy ((==) `on` f)
                . sortBy (comparing f)

-- | /O(n log n)/ nub by a comparison function. Destroys ordering
nubSortedOn :: Ord b => (a -> b) -> [a] -> [a]
nubSortedOn f = map head . groupSortedOn f

