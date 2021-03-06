{-# LANGUAGE TemplateHaskell, FlexibleContexts, DeriveFunctor #-}
-- | Types
module Induction.Structural.Types
    (
    -- * Obligations
      Obligation(..), TaggedObligation,
      Predicate,
      Hypothesis,
    -- ** Terms
      Term(..),
    -- * Typing environment
      TyEnv,
    -- ** Arguments
      Arg(..),
    -- * Tagged (fresh) variables
      Tagged(..), tag,
    -- ** Removing tagged variables
      unTag, unTagM, unTagMapM
    ) where

import Data.Generics.Genifunctors

import Control.Monad.Identity
import Control.Monad.State
import Control.Applicative

import Data.Function (on)

import Data.Traversable (traverse)

import Data.Map (Map)
import qualified Data.Map as M

-- | The simple term language only includes variables, constructors and functions.
data Term c v
    = Var v
    | Con c [Term c v]
    | Fun v [Term c v]
    -- ^ Induction on exponential data types yield assumptions with functions
  deriving (Eq,Ord,Functor)

-- Typed variables are represented as (v,t)

-- | A list of terms.
--
-- Example: @[tm1,tm2]@ corresponds to the formula /P(tm1,tm2)/
type Predicate c v = [Term c v]

-- | Quantifier lists are represented as tuples of variables and their type.
--
-- Example:
--
--
-- >Obligation
-- >    { implicit   = [(x,t1),(y,t2)]
-- >    , hypotheses = [([],[htm1,htm2])
-- >                   ,([(z,t3)],[htm3,htm4])
-- >                   ]
-- >    , conclusion = [tm1,tm2]
-- >    }
--
-- Corresponds to the formula:
--
-- /forall (x : t1) (y : t2) . (P(htm1,htm2) & (forall (z : t3) . P(htm3,htm4)) => P(tm1,tm2))/
--
-- The implicit variables (/x/ and /y/) can be viewed as skolemised, and use
-- these three formulae instead:
--
-- /P(htm1,htm2)./
--
-- /forall (z : t3) . P(htm3,htm4)./
--
-- /~ P(tm1,tm2)./
--
data Obligation c v t = Obligation
    { implicit   :: [(v,t)]
    -- ^ Implicitly quantified variables (skolemised)
    , hypotheses :: [Hypothesis c v t]
    -- ^ Hypotheses, with explicitly quantified variables
    , conclusion :: Predicate c v
    -- ^ The induction conclusion
    }
    deriving (Functor)

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


-- | An argument to a constructor can be recursive (`Rec`) or non-recursive
-- (`NonRec`).  Induction hypotheses will be asserted for `Rec` arguments.
--
-- For instance, when doing induction on @[a]@, then @(:)@ has two arguments,
-- @NonRec a@ and @Rec [a]@. On the other hand, if doing induction on @[Nat]@,
-- then @(:)@ has @NonRec Nat@ and @Rec [Nat]@.
--
-- Data types can also be exponential. Consider
--
-- @data Ord = Zero | Succ Ord | Lim (Nat -> Ord)@
--
-- Here, the @Lim@ constructor is exponential. If we describe types and
-- constructors with strings, the constructors for this data type is:
--
-- >[ ("Zero",[])
-- >, ("Succ",[Rec "Ord"])
-- >, ("Lim",[Exp ("Nat -> Ord") ["Nat"])
-- >]
--
-- The first argument to `Exp` is the type of the function, and the second
-- argument are the arguments to the function.
data Arg t
    = Rec t
    | NonRec t
    | Exp t [t]

-- | Given a type, return either that you cannot do induction on is type
-- (`Nothing`), or `Just` the constructors and a description of their arguments
-- (see `Arg`).
--
-- The function /should instantiate type variables/. For instance, if you look
-- up the type @[Nat]@, you should return the cons constructor with arguments
-- @Nat@ and @[Nat]@ (see `Arg`).
--
-- Examples of types not possible to do induction on are function spaces and
-- type variables. For these, return `Nothing`.
type TyEnv c t = t -> Maybe [(c,[Arg t])]

-- | Cheap way of introducing fresh variables. The `Eq` and `Ord` instances
-- only uses the `Integer` tag.
data Tagged v = v :~ Integer

-- | The `Integer` tag
tag :: Tagged v -> Integer
tag (_ :~ t) = t

instance Eq (Tagged v) where
    (==) = (==) `on` tag

instance Ord (Tagged v) where
    compare = compare `on` tag

-- | Obligations with tagged variables (see `Tagged` and `unTag`)
type TaggedObligation c v t = Obligation c (Tagged v) t

return []

-- | Tri-traverse of Obligation
trObligation :: Applicative f => (c -> f c') -> (v -> f v') -> (t -> f t') -> Obligation c v t -> f (Obligation c' v' t')
trObligation = $(genTraverse ''Obligation)

-- | Removing tagged (fresh) variables in a monad.
-- The remove function is exectued at /every occurence/ of a tagged variable.
-- This is useful if you want to sync it with your own name supply monad.
unTagM :: Applicative m => (Tagged v -> m v') -> [TaggedObligation c v t] -> m [Obligation c v' t]
unTagM f = traverse (trObligation pure f pure)

-- | Removing tagged (fresh) variables
unTag :: (Tagged v -> v') -> [TaggedObligation c v t] -> [Obligation c v' t]
unTag f = runIdentity . unTagM (return . f)

-- | Remove tagged (fresh) variables in a monad.
-- The remove function is exectued /only once/ for each tagged variable,
-- and a `Map` of renamings is returned.
-- This is useful if you want to sync it with your own name supply monad.
unTagMapM :: (Functor m,Monad m) => (Tagged v -> m v') -> [TaggedObligation c v t]
         -> m ([Obligation c v' t],Map (Tagged v) v')
unTagMapM f = flip runStateT M.empty . unTagM f'
  where
    f' tv = do
        m <- get
        case M.lookup tv m of
            Just v' -> return v'
            Nothing -> do
                v' <- lift (f tv)
                modify (M.insert tv v')
                return v'

