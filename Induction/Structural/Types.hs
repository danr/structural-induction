-- | Types
{-# LANGUAGE
      TemplateHaskell,
      PatternGuards,
      ExplicitForAll,
      MultiParamTypeClasses,
      ScopedTypeVariables,
      TypeOperators,
      FlexibleInstances
  #-}
module Induction.Structural.Types
    (
    -- * Obligations
      IndPart(..), IndPartV,
      Predicate,
      Hypothesis,
    -- ** Terms
      Term(..),
    -- * Typing environment
      TyEnv,
    -- ** Arguments
      Arg(..),
    -- * Fresh variables
      V,
    -- ** Removing fresh variables
      unV, unVM
    ) where

import Control.Monad.Identity

import Induction.Structural.Auxiliary ((.:))

import Data.Generics.Geniplate

-- | Terms
--
-- The simple term language only includes variables, constructors and functions.
data Term c v
    = Var v
    | Con c [Term c v]
    | Fun v [Term c v]
    -- ^ Induction on exponential data types yield assumptions with functions
  deriving (Eq,Ord,Show)

-- Geniplate Instances

instanceTransformBi [t| forall c v . (Term c v,Term c v) |]
instanceUniverseBi  [t| forall c v . (Term c v,Term c v) |]


-- Typed variables are represented as (v,t)

-- | A list of terms.
--
-- Example: @[tm1,tm2]@ corresponds to the formula /P(tm1,tm2)/
type Predicate c v = [Term c v]

-- | Induction part data type
--
-- Quantifier lists are represented as tuples of variables and their type.
data IndPart c v t = IndPart
    { implicit   :: [(v,t)]
    -- ^ Implicitly quantified variables (skolemised)
    , hypotheses :: [Hypothesis c v t]
    -- ^ Hypotheses, with explicitly quantified variables
    , conclusion :: Predicate c v
    -- ^ The induction conclusion
    }

-- | Quantifier lists are represented as tuples of variables and their type.
--
-- Example:
--
-- @([(x,t1),(y,t2)],[tm1,tm2])@
--
-- corresponds to the formula
--
-- /forall (x : t1) (y : t2) . P(tm1,tm2)/
type Hypothesis c v t = ([(v,t)],Predicate c v)


{-| Arguments

    An argument to a constructor can be recursive or non-recursive.

    For instance, when doing induction on [a], then (:) has two arguments,
    NonRec a and Rec [a].

    If doing induction on [Nat], then (:) has NonRec Nat and Rec [Nat]

    So Rec signals that there should be emitted an induction hypothesis here.

    Data types can also be exponential. Consider

    @
        data Ord = Zero | Succ Ord | Lim (Nat -> Ord)
    @

    Here, the Lim constructor is exponential, create it with

    @
        Exp (Nat -> Ord) [Nat]
    @

    The first argument is the type of the function, and the second
    argument are the arguments to the function. The apparent duplication
    is there because the type is kept entirely abstract in this module.
-}
data Arg t
    = Rec t
    | NonRec t
    | Exp t [t]
  deriving (Eq,Ord,Show)

{-| Type environment

    Given a type, returns the constructors and the types of their arguments,
    and also if the arguments are recursive, non-recursive or exponential (see Arg).

    The function should instantiate type variables.
    For instance, looking up the type List Nat, should return the constructors
    Nil with args [], and Cons with args [NonRec Nat,Rec (List Nat)].

    If it is not possible to do induction on this type, return Nothing.
    Examples are function spaces and type variables.

-}

type TyEnv c t = t -> Maybe [(c,[Arg t])]

-- | Cheap way of introducing fresh variables
type V v = (v,Integer)

-- | Obligations with tagged variables (see `V`)
type IndPartV c v t = IndPart c (V v) t

-- | Removing the fresh variables, in a monad
unVM :: Monad m => (v -> Integer -> m v) -> IndPartV c v t -> m (IndPart c v t)
unVM f (IndPart skolem hyps concl)
    = IndPart <$> unQuant skolem
              <*> mapM (\(qs,hyp) -> (,) <$> unQuant qs <*> mapM unTm hyp) hyps
              <*> mapM unTm concl
  where
    (<$>) = liftM
    (<*>) = ap

    f' = uncurry f

    unQuant = mapM (\(v,t) -> (,) <$> f' v <*> return t)

    unTm tm = case tm of
        Var x     -> Var <$> f' x
        Con c tms -> Con c <$> mapM unTm tms
        Fun x tms -> Fun <$> f' x <*> mapM unTm tms

-- | Removing the fresh variables
unV :: (v -> Integer -> v) -> IndPartV c v t -> IndPart c v t
unV f = runIdentity . unVM (return .: f)

