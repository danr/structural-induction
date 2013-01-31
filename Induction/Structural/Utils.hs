{-# OPTIONS_HADDOCK hide #-}
-- | Internal utility functions (pertaining to data types in this library)
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Induction.Structural.Utils where

import Control.Applicative hiding (empty)
import Control.Monad.State

import Induction.Structural.Types

-- | Tagged terms
type TaggedTerm c v = Term c (Tagged v)

-- | Tagged hypotheses
type TaggedHypothesis c v t = Hypothesis c (Tagged v) t

-- | Get the representation of the argument
argRepr :: Arg t -> t
argRepr (Rec t)    = t
argRepr (NonRec t) = t
argRepr (Exp t _)  = t

-- Fresh variables

-- | A monad of fresh Integers
newtype Fresh a = Fresh (State Integer a)
  deriving (Functor,Applicative,Monad,MonadState Integer)

-- | Run the fresh monad
runFresh :: Fresh a -> a
runFresh (Fresh m) = evalState m 0

-- | Creating a fresh variable
newFresh :: v -> Fresh (Tagged v)
newFresh v = Fresh $ state $ \ s -> ((v,s),s+1)

-- | Create a fresh variable that has a type
newTyped :: v -> t -> Fresh (Tagged v,t)
newTyped v t = flip (,) t <$> newFresh v

-- | Refresh variable
refreshTagged :: Tagged v -> Fresh (Tagged v)
refreshTagged (v,_) = newFresh v

-- | Refresh a variable that has a type
refreshTypedTagged :: Tagged v -> t -> Fresh (Tagged v,t)
refreshTypedTagged v t = flip (,) t <$> refreshTagged v

