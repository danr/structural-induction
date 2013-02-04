module Mini where

import Induction.Structural

testEnv :: TyEnv String String
testEnv "Nat" = Just [ ("zero",[]) , ("succ",[Rec "Nat"]) ]
testEnv _ = Nothing

natInd :: [String] -> [Int] -> IO ()
natInd vars coords = putStrLn
    $ render
    $ linObligations strStyle
    $ unTag (\(x :~ i) -> x ++ show i)
    $ subtermInduction testEnv typed_vars coords
  where
    typed_vars = zip vars (repeat "Nat")

