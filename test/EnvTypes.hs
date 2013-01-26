{-# LANGUAGE GADTs, KindSignatures, FlexibleInstances, ConstraintKinds, PatternGuards #-}
module EnvTypes where

import Nat

import Data.Function (on)

import Test.QuickCheck
import Util

type EqShow a = (Eq a,Show a)

data Sigma :: (* -> *) -> * where
    Si :: EqShow a => r a -> Sigma r

data Exists :: (* -> *) -> * where
    Val :: EqShow a => r a -> a -> Exists r

-- Representations of our types.
-- Putting Eq and Show here simplifies those instances for Repr a bit
data Repr a where
    Nat   :: Repr Nat
    PInt  :: Repr PInt
    Bool  :: Repr Bool
    List  :: EqShow a => Repr a -> Repr [a]
    Maybe :: EqShow a => Repr a -> Repr (Maybe a)
    TupTy :: (EqShow a,EqShow b) => Repr a -> Repr b -> Repr (a,b)
    TyVar :: Repr Int
    -- ^ Should this contain more information?

instance Show Ty' where
    show (Si r) = case r of
        Nat       -> "Nat"
        PInt      -> "Int"
        Bool      -> "Bool"
        List a    -> "[" ++ show (Si a) ++ "]"
        Maybe a   -> "Maybe " ++ show (Si a)
        TupTy a b -> "(" ++ show (Si a) ++ "," ++ show (Si b) ++ ")"
        TyVar     -> "a"

instance Arbitrary Ty' where
    arbitrary = halfSize $ \ s -> frequency
        [ (10,return $ Si Nat)
        , (2,return $ Si PInt)
        , (1,return $ Si Bool)
        , (1,return $ Si TyVar)
        , (s,do
            Si a <- arbitrary
            return $ Si (List a))
        , (s `div` 2,do
            Si a <- arbitrary
            return $ Si (Maybe a))
        , (s,do
            Si a <- arbitrary
            Si b <- arbitrary
            return $ Si (TupTy a b))
        ]

    shrink (Si (List a))    = Si a:shrink (Si a)
    shrink (Si (TupTy a b)) = Si a:Si b:(shrink (Si a) ++ shrink (Si b))
    shrink (Si (Maybe a))   = Si a:shrink (Si a)
    shrink (Si PInt)        = [Si Nat]
    shrink (Si Nat)         = [Si Bool]
    shrink (Si TyVar)       = []
    shrink _                = [Si TyVar]

data Con a where
    Zero :: Con Nat
    Succ :: Con Nat
    Pos  :: Con PInt
    Neg  :: Con PInt
    Tru  :: Con Bool
    Fls  :: Con Bool
    Nil  :: EqShow a => Repr a -> Con [a]
    Cons :: Con [a]
    Jst  :: Con (Maybe a)
    Ntng :: EqShow a => Repr a -> Con (Maybe a)
    Tup  :: Con (a,b)

infoCon' :: Con' -> (Int,String)
infoCon' c = case c of
    Si Zero   -> (0,"Zero")
    Si Succ   -> (1,"Succ")
    Si Nil{}  -> (2,"Nil")
    Si Cons   -> (3,"Cons")
    Si Pos    -> (4,"Pos")
    Si Neg    -> (5,"Neg")
    Si Jst    -> (6,"Just")
    Si Ntng{} -> (7,"Nothing")
    Si Tru    -> (8,"True")
    Si Fls    -> (9,"False")
    Si Tup    -> (10,"Tup")

instance Eq Con' where
    (==) = (==) `on` (fst . infoCon')

instance Ord Con' where
    compare = compare `on` (fst . infoCon')

instance Show Con' where
    show = snd . infoCon'


type Repr' = Exists Repr

type Ty' = Sigma Repr

type Con' = Sigma Con

instance Show (Exists a) where
    show (Val _ x) = show x

data Equal :: * -> * -> * where
    Refl :: Equal a a

(==?) :: Repr a -> Repr b -> Maybe (Equal a b)
Nat     ==? Nat   = Just Refl
PInt    ==? PInt  = Just Refl
Bool    ==? Bool  = Just Refl
TyVar   ==? TyVar = Just Refl
Maybe a ==? Maybe b     | Just Refl <- a ==? b = Just Refl
List a  ==? List b      | Just Refl <- a ==? b = Just Refl
TupTy a u ==? TupTy b v | Just Refl <- a ==? b
                        , Just Refl <- u ==? v = Just Refl
_      ==? _      = Nothing

instance Eq (Exists Repr) where
    Val s u == Val t v = case s ==? t of
        Just Refl -> u == v
        Nothing   -> False

