{-# LANGUAGE GADTs, KindSignatures, FlexibleInstances, ConstraintKinds, PatternGuards #-}
module EnvTypes where

import Nat

import Data.Function (on)

import Test.QuickCheck
import Util

type EqShow a = (Eq a,Show a,Arbitrary a)

data Sigma :: (* -> *) -> * where
    Si :: EqShow a => r a -> Sigma r

data Exists :: (* -> *) -> * where
    Val :: EqShow a => r a -> a -> Exists r

-- Representations of our types.
-- Putting Eq and Show here simplifies those instances for Repr a bit
data Repr a where
    Unit  :: Repr ()
    Nat   :: Repr Nat
    PInt  :: Repr PInt
    Bool  :: Repr Bool
    List  :: EqShow a => Repr a -> Repr [a]
    Maybe :: EqShow a => Repr a -> Repr (Maybe a)
    TupTy :: (EqShow a,EqShow b) => Repr a -> Repr b -> Repr (a,b)
    TyVar :: Repr Int
    -- ^ Should this contain more information?

showRepr :: Repr a -> String
showRepr r = case r of
    Unit      -> "Unit"
    Nat       -> "Nat"
    PInt      -> "PInt"
    Bool      -> "Bool"
    List a    -> "List " ++ showRepr a
    Maybe a   -> "Maybe " ++ showRepr a
    TupTy a b -> "TupTy " ++ showRepr a ++ " " ++ showRepr b
    TyVar     -> "TyVar"

showRepr' :: Repr' -> String
showRepr' (Val r x) = "Val " ++ showRepr r ++ " " ++ show x

instance Show Ty' where
    show (Si r) = case r of
        Unit      -> "()"
        Nat       -> "Nat"
        PInt      -> "Int"
        Bool      -> "Bool"
        List a    -> "[" ++ show (Si a) ++ "]"
        Maybe a   -> "Maybe " ++ show (Si a)
        TupTy a b -> "(" ++ show (Si a) ++ "," ++ show (Si b) ++ ")"
        TyVar     -> "a"

instance Arbitrary Ty' where
    arbitrary = halfSize $ \ s -> frequency
        [ (100,return $ Si Nat)
        , (20,return $ Si PInt)
        , (10,return $ Si Bool)
        , (10,return $ Si TyVar)
        , (1,return $ Si Unit)
        , (s * 25,do
            Si a <- arbitrary
            return $ Si (List a))
        , (s * 10,do
            Si a <- arbitrary
            return $ Si (Maybe a))
        , (s * 10,do
            Si a <- arbitrary
            Si b <- arbitrary
            return $ Si (TupTy a b))
        ]

    shrink (Si (List a))    = Si a:shrink (Si a)
    shrink (Si (TupTy a b)) = Si a:Si b:(shrink (Si a) ++ shrink (Si b))
    shrink (Si (Maybe a))   = Si a:shrink (Si a)
    shrink (Si PInt)        = [Si Nat]
    shrink (Si Nat)         = [Si Bool]
    shrink _                = [Si Unit]

data Con a where
    TT   :: Con ()
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
    Si TT     -> (0,"()")
    Si Zero   -> (1,"Zero")
    Si Succ   -> (2,"Succ")
    Si Nil{}  -> (3,"Nil")
    Si Cons   -> (4,"Cons")
    Si Pos    -> (5,"Pos")
    Si Neg    -> (6,"Neg")
    Si Jst    -> (7,"Just")
    Si Ntng{} -> (8,"Nothing")
    Si Tru    -> (9,"True")
    Si Fls    -> (10,"False")
    Si Tup    -> (11,"Tup")

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

shrinkRepr' :: Repr' -> [Repr']
shrinkRepr' (Val r x) = map (Val r) (shrink x)

data Equal :: * -> * -> * where
    Refl :: Equal a a

(==?) :: Repr a -> Repr b -> Maybe (Equal a b)
Unit      ==? Unit  = Just Refl
Nat       ==? Nat   = Just Refl
PInt      ==? PInt  = Just Refl
Bool      ==? Bool  = Just Refl
TyVar     ==? TyVar = Just Refl
Maybe a   ==? Maybe b   | Just Refl <- a ==? b = Just Refl
List a    ==? List b    | Just Refl <- a ==? b = Just Refl
TupTy a u ==? TupTy b v | Just Refl <- a ==? b
                        , Just Refl <- u ==? v = Just Refl
_         ==? _     = Nothing

instance Eq (Exists Repr) where
    Val s u == Val t v = case s ==? t of
        Just Refl -> u == v
        Nothing   -> False

