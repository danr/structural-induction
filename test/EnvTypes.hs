{-# LANGUAGE GADTs, KindSignatures, DeriveDataTypeable,
        FlexibleInstances, ConstraintKinds,
        PatternGuards, TemplateHaskell #-}
module EnvTypes where

import Nat

import Data.Function (on)
import Data.Typeable

import Test.QuickCheck
import Test.Feat

type EqShow a = (Eq a,Show a,Arbitrary a)

data Sigma :: (* -> *) -> * where
    Si :: EqShow a => r a -> Sigma r

data Exists :: (* -> *) -> * where
    Val :: EqShow a => r a -> a -> Exists r

type Repr' = Exists Repr

type Ty' = Sigma Repr


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
  deriving Typeable

data URepr
    = UUnit | UNat | UPInt | UBool
    | UList URepr | UMaybe URepr
    | UTupTy URepr URepr
    | UTyVar
  deriving Typeable

deriveEnumerable ''URepr

toTy :: URepr -> Ty'
toTy u = case u of
    UUnit      -> Si Unit
    UNat       -> Si Nat
    UPInt      -> Si PInt
    UBool      -> Si Bool
    UList a    | Si a' <- toTy a -> Si (List a')
    UMaybe a   | Si a' <- toTy a -> Si (Maybe a')
    UTupTy a b | Si a' <- toTy a
               , Si b' <- toTy b -> Si (TupTy a' b')
    UTyVar     -> Si TyVar

enumTy' :: Enumerate Ty'
enumTy' = fmap toTy enumerate

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

type Con' = Sigma Con

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

