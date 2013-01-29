{-# LANGUAGE
      TemplateHaskell,
      PatternGuards,
      ExplicitForAll,
      MultiParamTypeClasses,
      ScopedTypeVariables,
      TypeOperators
  #-}
module Induction.Structural.Types
    ( Term(..)   , TermV
    , Hypothesis , HypothesisV
    , Predicate
    , IndPart(..), IndPartV
    , (:::)
    , Arg(..)
    , argRepr
    , unV
    , unVM
    , TyEnv
    , V
    , Fresh
    ) where

import Control.Applicative hiding (empty)
import Control.Monad.State
import Control.Monad.Identity

import Induction.Structural.Auxiliary ((.:))

import Data.Generics.Geniplate

-- Terms

data Term c v
    = Var { termVarName :: v }
    | Con { termConName :: c , termArgs :: [Term c v] }
    | Fun { termFunName :: v , termArgs :: [Term c v] }
    -- ^ Exponential datatypes yield functions
  deriving (Eq,Ord,Show)

-- Geniplate Instances

instanceTransformBi [t| forall c v . (Term c v,Term c v) |]
instanceUniverseBi  [t| forall c v . (Term c v,Term c v) |]


-- Typed variables
type v ::: t = (v,t)

-- | Induction predicate type
--
-- The abstract predicate P is of some arity, and the arguments are in a list
type Predicate c v = [Term c v]

-- | Induction part data type
data IndPart c v t = IndPart
    { implicit   :: [v ::: t]
    , hypotheses :: [Hypothesis c v t]
    , conclusion :: Predicate c v
    }
  deriving(Eq,Ord,Show)

-- | Hypotheses
type Hypothesis c v t = ([v ::: t],Predicate c v)


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

-- | Get the representation of the argument
argRepr :: Arg t -> t
argRepr (Rec t)    = t
argRepr (NonRec t) = t
argRepr (Exp t _)  = t

{-| Type environment

    Given a type, returns the constructors and the types of their arguments,
    and also if the arguments are recursive, non-recursive or exponential (see Arg).

    The function should instantiate type variables.
    For instance, looking up the type List Nat, should return the constructors
    Nil with args [], and Cons with args [NonRec Nat,Rec (List Nat)].

    If it is not possible to do induction on this type, return Nothing.
    Examples are function spaces and type variables.

-}

type TyEnv c t = t -> Maybe [c ::: [Arg t]]

-- Fresh variables

-- | A monad of fresh Integers
type Fresh = State Integer

-- | Cheap way of introducing fresh variables
type V v = (v,Integer)

-- | Our datatypes with tagged variables
type IndPartV c v t = IndPart c (V v) t
type TermV c v = Term c (V v)
type HypothesisV c v t = Hypothesis c (V v) t

-- Removing fresh variables

-- | Flattens out fresh variable names, in a monad
unVM :: (Applicative m,Monad m)
     => (v -> Integer -> m v) -> IndPartV c v t -> m (IndPart c v t)
unVM f (IndPart skolem hyps concl)
    = IndPart <$> unQuant skolem
              <*> mapM (\(qs,hyp) -> (,) <$> unQuant qs <*> mapM unTm hyp) hyps
              <*> mapM unTm concl
  where
    f' = uncurry f

    unQuant = mapM (\(v,t) -> (,) <$> f' v <*> return t)

    unTm tm = case tm of
        Var x     -> Var <$> f' x
        Con c tms -> Con c <$> mapM unTm tms
        Fun x tms -> Fun <$> f' x <*> mapM unTm tms

-- | Flatten out fresh variable names
unV :: (v -> Integer -> v) -> IndPartV c v t -> IndPart c v t
unV f = runIdentity . unVM (return .: f)


