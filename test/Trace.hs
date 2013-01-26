module Trace where

import Data.List (find)
import Control.Monad (mplus,msum)

data Trace a = Fork a [Trace a]

instance Show a => Show (Trace a) where
    show = unlines . go
      where
        go (Fork x ts) = show x:bars (map go ts)

        bar :: [String] -> [String]
        bar [] = []
        bar (s:xs) = ("┣┉" ++ s):map ("┃ " ++) xs

        bars :: [[String]] -> [String]
        bars [] = []
        bars [s:xs] = ("┗┉" ++ s):map ("  " ++) xs
        bars (x:xs) = bar x ++ bars xs

loop :: Eq a => Trace a -> Maybe a
loop = go []
  where
    go vis (Fork x ts) = find (x ==) vis `mplus` msum (map (go (x:vis)) ts)

