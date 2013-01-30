{-# LANGUAGE ScopedTypeVariables, TypeOperators, PatternGuards, GeneralizedNewtypeDeriving #-}
module Induction.Structural.Utils
    ( Fresh
    , runFresh
    , newFresh
    , newTyped
    , refreshV
    , refreshTypedV
    , tidy
    , mdelete
    , quantify
    -- * Args
    , termArgs
    , argRepr
    , isRec
    -- * Terms
    , varFree
    , substList
    , subst
    ) where

import Control.Arrow hiding ((<+>))
import Control.Applicative hiding (empty)
import Control.Monad.State

import Induction.Structural.Auxiliary (nubSortedOn)
import Induction.Structural.Types

import Data.Generics.Geniplate

-- | Delete a varibale from a type environment
mdelete :: Eq a => a -> [a ::: b] -> [a ::: b]
mdelete x = filter (\ (y,_) -> x /= y)

-- | Quantify in a hypothesis
quantify :: Ord v => [v ::: t] -> Hypothesis c v t -> Hypothesis c v t
quantify xs (ys,hyp) = ([(x,t) | (x,t) <- xs, any (x `varFree`) hyp] ++ ys,hyp)

-- | Tidy up hypotheses
tidy :: (Ord c,Ord v) => [Hypothesis c v t] -> [Hypothesis c v t]
tidy = nubSortedOn (first (map fst)) . filter (not . all isAtom . snd)
  where
    isAtom (Con _ tms) = all isAtom tms
    isAtom _           = False

-- Fresh variables

-- | A monad of fresh Integers
newtype Fresh a = Fresh (State Integer a)
  deriving (Functor,Applicative,Monad,MonadState Integer)

runFresh :: Fresh a -> a
runFresh (Fresh m) = evalState m 0

-- | Creating a fresh variable
newFresh :: v -> Fresh (V v)
newFresh v = Fresh $ state $ \ s -> ((v,s),s+1)

-- | Create a fresh variable that has a type
newTyped :: v -> t -> Fresh (V v ::: t)
newTyped v t = flip (,) t <$> newFresh v

-- | Refresh variable
refreshV :: V v -> Fresh (V v)
refreshV (v,_) = newFresh v

-- | Refresh a variable that has a type
refreshTypedV :: V v -> t -> Fresh (V v ::: t)
refreshTypedV v t = flip (,) t <$> refreshV v

-- * Arguments

-- | Get the representation of the argument
argRepr :: Arg t -> t
argRepr (Rec t)    = t
argRepr (NonRec t) = t
argRepr (Exp t _)  = t

termArgs :: Term c v -> [Term c v]
termArgs (Var _)    = []
termArgs (Con _ xs) = xs
termArgs (Fun _ xs) = xs

isRec :: Arg t -> Bool
isRec Rec{} = True
isRec _     = False


-- * Terms

-- | Does this variable occur in this term?
varFree :: Eq v => v -> Term c v -> Bool
varFree v tm = or $ [ v == v' | Var v'   <- universe tm ]
                 ++ [ v == v' | Fun v' _ <- universe tm ]

-- Substitution of terms

-- | Substitution on many variables.
--
-- The rhs of the substitution must be only fresh variables.
substList :: Eq v => [(v,Term c v)] -> Term c v -> Term c v
substList subs = transformBi $ \ tm ->
    case tm of
        Var x | Just tm' <- lookup x subs -> tm'
        _                                 -> tm

-- | Substitution.
--
-- The rhs of the substitution must be only fresh variables.
subst :: Eq v => v -> Term c v -> Term c v -> Term c v
subst x t = substList [(x,t)]

