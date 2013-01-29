{-# LANGUAGE ScopedTypeVariables, TypeOperators, PatternGuards #-}
module Induction.Structural.Utils
    ( V
    , Fresh
    , newFresh
    , newTyped
    , refreshV
    , refreshTypedV
    , tidy
    , mdelete
    , quantify
    , argRepr
    -- Terms
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

-- | Tidy up hypethoses
tidy :: (Ord c,Ord v) => [Hypothesis c v t] -> [Hypothesis c v t]
tidy = nubSortedOn (first (map fst)) . filter (not . all isAtom . snd)
  where
    isAtom (Con _ tms) = all isAtom tms
    isAtom _           = False

-- | Creating a fresh variable
newFresh :: v -> Fresh (V v)
newFresh v = do
    x <- get
    modify succ
    return (v,x)

-- | Create a fresh variable that has a type
newTyped :: v -> t -> Fresh (V v ::: t)
newTyped v t = flip (,) t <$> newFresh v

-- | Refresh variable
refreshV :: V v -> Fresh (V v)
refreshV (v,_) = newFresh v

-- | Refresh a variable that has a type
refreshTypedV :: V v -> t -> Fresh (V v ::: t)
refreshTypedV v t = flip (,) t <$> refreshV v

-- Terms

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

