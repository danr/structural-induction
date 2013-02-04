{-# LANGUAGE GADTs, ConstraintKinds, ExplicitForAll, PatternGuards #-}
module Env where

import Test.QuickCheck
import Control.Applicative

import Induction.Structural

import EnvTypes
import Nat
import Util

type Oblig = Obligation Con' String Ty'
type Tm    = Term Con' String
type P     = Predicate Con' String
type Hyp   = Hypothesis Con' String Ty'

-- | A small test environment. No exponentials for now.
testEnv :: Repr a -> Maybe [(Con a,[Arg Ty'])]
testEnv t = case t of
    Unit      -> Just [(TT,[])]
    Nat       -> Just [(Zero,[])
                      ,(Succ,[Rec (Si Nat)])
                      ]
    PInt      -> Just [(Pos,[NonRec (Si Nat)])
                      ,(Neg,[NonRec (Si Nat)])
                      ]
    Bool      -> Just [(Tru,[]),(Fls,[])]
    List a    -> Just [(Nil a,[])
                      ,(Cons,[NonRec (Si a),Rec (Si (List a))])
                      ]
    Maybe a   -> Just [(Ntng a,[])
                      ,(Jst,[NonRec (Si a)])
                      ]
    TupTy a b -> Just [(Tup,[NonRec (Si a),NonRec (Si b)])]
    TyVar     -> Nothing

-- | Forgetting some type info
testEnv' :: TyEnv Con' Ty'
testEnv' (Si t) = case testEnv t of
    Just ksargs -> Just (map (uncurry forget) ksargs)
    Nothing -> Nothing
  where
    forget :: forall a . EqShow a => Con a -> [Arg Ty'] -> (Con',[Arg Ty'])
    forget k args = (Si k, args)

-- | Generates a random value of some type
arbFromType :: Repr a -> Gen a
arbFromType t = case t of
    Unit   -> arbitrary
    Nat    -> arbitrary
    PInt   -> arbitrary
    Bool   -> arbitrary
    List a -> halfSize $ \ s -> frequency
        [ (1, return [])
        , (s, (:) <$> arbFromType a <*> arbFromType (List a))
        ]
    Maybe a -> sized $ \ s -> frequency
        [ (1, return Nothing)
        , (s, Just <$> arbFromType a)
        ]
    TupTy a b -> (,) <$> arbFromType a <*> arbFromType b
    TyVar -> arbitrary

-- | Forget type information
arbFromType' :: Sigma Repr -> Gen (Exists Repr)
arbFromType' (Si r) = Val r <$> arbFromType r

startFromTypes :: [Ty'] -> Gen [Repr']
startFromTypes = mapM arbFromType'

-- Cannot make this well typed in a nice way
mkCon :: Con' -> [Repr'] -> Repr'
mkCon (Si c) as = case c of
    TT     -> case as of { []                -> Val Unit ()            ; _ -> ill_typed }
    Zero   -> case as of { []                -> Val Nat Z              ; _ -> ill_typed }
    Succ   -> case as of { [Val Nat n]       -> Val Nat (S n)          ; _ -> ill_typed }
    Pos    -> case as of { [Val Nat n]       -> Val PInt (P n)         ; _ -> ill_typed }
    Neg    -> case as of { [Val Nat n]       -> Val PInt (N n)         ; _ -> ill_typed }
    Fls    -> case as of { []                -> Val Bool False         ; _ -> ill_typed }
    Tru    -> case as of { []                -> Val Bool True          ; _ -> ill_typed }
    Ntng a -> case as of { []                -> Val (Maybe a) Nothing  ; _ -> ill_typed }
    Jst    -> case as of { [Val a x]         -> Val (Maybe a) (Just x) ; _ -> ill_typed }
    Tup    -> case as of { [Val a x,Val b y] -> Val (TupTy a b) (x,y)  ; _ -> ill_typed }
    Nil a  -> case as of { []                -> Val (List a) []        ; _ -> ill_typed }
    Cons   -> case as of
        [Val a x,Val (List b) xs] -> case a ==? b of
            Just Refl -> Val (List a) (x:xs)
            Nothing   -> error $ "mkCon: " ++ show as ++ " is heterogenous!"
        _ -> ill_typed
  where
    ill_typed :: a
    ill_typed = error $ "mkCon: illtyped: " ++ show (Si c) ++ " on " ++ show as

type VarMap = [(String,Repr')]

-- | Tries to match a representation to a term, returning bound variables
match :: Repr' -> Tm -> Maybe VarMap
match v tm0 = case tm0 of
    Var s -> Just [(s,v)]
    Con (Si c) tms -> case (v,c,tms) of
        (Val Unit ()            , TT     , [])   -> ok
        (Val Nat Z              , Zero   , [])   -> ok
        (Val Nat (S x)          , Succ   , [tm]) -> match (Val Nat x) tm
        (Val PInt (P x)         , Pos    , [tm]) -> match (Val Nat x) tm
        (Val PInt (N x)         , Neg    , [tm]) -> match (Val Nat x) tm
        (Val Bool True          , Tru    , [])   -> ok
        (Val Bool False         , Fls    , [])   -> ok
        (Val (Maybe a) Nothing  , Ntng b , []) | Just Refl <- a ==? b -> ok
        (Val (Maybe a) (Just x) , Jst    , [tm]) -> match (Val a x) tm
        (Val (List a) []        , Nil b  , []) | Just Refl <- a ==? b -> ok
        (Val (List a) (x:xs)    , Cons   , [t1,t2]) ->
            match (Val a x) t1 `comb` match (Val (List a) xs) t2
        (Val (TupTy a b) (x,y)  , Tup    , [t1,t2]) ->
            match (Val a x) t1 `comb` match (Val b y) t2
        _ -> Nothing
    Fun{} -> error "match: No support for exponentials!"
  where
    ok = Just []
    comb r s = (++) <$> r <*> s

-- | Show induction schema
showOblig :: [Oblig] -> String
showOblig = unlines . map ((++ ".") . render . linObligation style)

-- | The style for printing
style :: Style Con' String Ty'
style = Style (text . show) text (text . show)

