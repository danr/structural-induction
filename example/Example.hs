module Example where

import Induction.Structural

-- | A small test envirenment of Ordinals, Naturals, Integers,
--   Lists, Trees and Expressions.
testEnv :: TyEnv String String
testEnv t = case t of
    "Ord" -> Just [("zero",[])
                  ,("succ",[Rec "Ord"])
                  ,("lim",[Exp "Nat -> Ord" ["Nat"]])
                  ]
    "Nat" -> Just [("zero",[])
                  ,("succ",[Rec "Nat"])
                  ]
    "Int" -> Just [("pos",[NonRec "Nat"])
                  ,("neg",[NonRec "Nat"])
                  ]
    _ | ("List ",a) <- splitAt 5 t ->
            Just [("nil",[])
                 ,("cons",[NonRec a,Rec t])
                 ]
      | ("Tree ",a) <- splitAt 5 t ->
            Just [("leaf",[NonRec a])
                 ,("fork",[Rec t,Rec t])
                 ]
      | ("Tree' ",a) <- splitAt 6 t ->
            Just [("empty",[])
                 ,("branch",[Rec t,NonRec a,Rec t])
                 ]
      | ("Expr ",v) <- splitAt 5 t ->
            Just [("var",[NonRec v])
                 ,("lit",[NonRec "Int"])
                 ,("add",[Rec t,Rec t])
                 ,("mul",[Rec t,Rec t])
                 ,("neg",[Rec t,Rec t])
                 ]
    _ -> Nothing

-- | Specify the type of every variable, then on which coordinates of
--   P to do induction on. This function then takes care of the
--   plumbing and prints the results.
testStrInd :: [(String,String)] -> [Int] -> IO ()
testStrInd vars coords = putStrLn
    $ render
    $ linObligations strStyle
    $ unTag (\(x :~ i) -> x ++ show i)
    $ subtermInduction testEnv vars coords

-- Various tests --------------------------------------------------------------

intInd      = testStrInd [("X","Int")]

intInd2     = testStrInd [("X","Int"),("Y","Int")]

intInd3     = testStrInd [("X","Int"),("Y","Int"),("Z","Int")]

natInd      = testStrInd [("X","Nat")]

natInd2     = testStrInd [("X","Nat"),("Y","Nat")]

natInd3     = testStrInd [("X","Nat"),("Y","Nat"),("Z","Nat")]

listInd     = testStrInd [("Xs","List a")]

natListInd  = testStrInd [("Xs","List Nat")]

ordListInd  = testStrInd [("Xs","List Ord")]

ordInd      = testStrInd [("X","Ord")]

treeInd     = testStrInd [("T","Tree a")]

exprInd     = testStrInd [("E","Expr a")]

tree'Ind    = testStrInd [("T","Tree' a")]

treeTreeInd = testStrInd [("T","Tree Tree a")]

