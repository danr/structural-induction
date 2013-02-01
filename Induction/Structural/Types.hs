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

import Control.Monad.Identity
import Control.Monad.State

import Induction.Structural.Auxiliary ((.:))

import Data.Function (on)

import Data.Map (Map)
import qualified Data.Map as M

-- | Terms
--
-- The simple term language only includes variables, constructors and functions.
data Term c v
    = Var v
    | Con c [Term c v]
    | Fun v [Term c v]
    -- ^ Induction on exponential data types yield assumptions with functions
  deriving (Eq,Ord,Show)

-- Typed variables are represented as (v,t)

-- | A list of terms.
--
-- Example: @[tm1,tm2]@ corresponds to the formula /P(tm1,tm2)/
type Predicate c v = [Term c v]

-- | Obligations
--
-- Quantifier lists are represented as tuples of variables and their type.
data Obligation c v t = Obligation
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


-- | Arguments
--
-- An argument to a constructor can be recursive or non-recursive.
--
-- For instance, when doing induction on [a], then (:) has two arguments,
-- NonRec a and Rec [a].
--
-- If doing induction on [Nat], then (:) has NonRec Nat and Rec [Nat]
--
-- So Rec signals that there should be emitted an induction hypothesis here.
--
-- Data types can also be exponential. Consider
--
-- @
--     data Ord = Zero | Succ Ord | Lim (Nat -> Ord)
-- @
--
-- Here, the Lim constructor is exponential, create it with
--
-- @
--     Exp (Nat -> Ord) [Nat]
-- @
--
-- The first argument is the type of the function, and the second
-- argument are the arguments to the function. The apparent duplication
-- is there because the type is kept entirely abstract in this module.
data Arg t
    = Rec t
    | NonRec t
    | Exp t [t]

-- | Type environment
--
-- Given a type, returns the constructors and the types of their arguments,
-- and also if the arguments are recursive, non-recursive or exponential (see Arg).
--
-- The function should instantiate type variables.
-- For instance, looking up the type List Nat, should return the constructors
-- Nil with args [], and Cons with args [NonRec Nat,Rec (List Nat)].
--
-- If it is not possible to do induction on this type, return Nothing.
-- Examples are function spaces and type variables.
type TyEnv c t = t -> Maybe [(c,[Arg t])]

-- | Cheap way of introducing fresh variables
data Tagged v = v :~ Integer

tag :: Tagged v -> Integer
tag (v :~ t) = t

instance Eq (Tagged v) where
    (==) = (==) `on` tag

instance Ord (Tagged v) where
    compare = compare `on` tag

-- | Obligations with tagged variables (see `Tagged` and `unTag`)
type TaggedObligation c v t = Obligation c (Tagged v) t

-- | Removing tagged (fresh) variables, in a monad
--
-- The remove function is exectued at every occurence of a tagged variable.
--
-- This is useful if you want to sync it with your own name supply monad.
unTagM :: Monad m => (Tagged v -> m v') -> [TaggedObligation c v t] -> m [Obligation c v' t]
unTagM f = mapM $ \ (Obligation skolem hyps concl) ->
    Obligation <$> unQuant skolem
               <*> mapM (\(qs,hyp) -> (,) <$> unQuant qs <*> mapM unTm hyp) hyps
               <*> mapM unTm concl
  where
    (<$>) = liftM
    (<*>) = ap

    unQuant = mapM (\(v,t) -> (,) <$> f v <*> return t)

    unTm tm = case tm of
        Var x     -> Var <$> f x
        Con c tms -> Con c <$> mapM unTm tms
        Fun x tms -> Fun <$> f x <*> mapM unTm tms
-- This function could be tested for being the identity on (,)

-- | Removing tagged (fresh) variables
unTag :: (Tagged v -> v') -> [TaggedObligation c v t] -> [Obligation c v' t]
unTag f = runIdentity . unTagM (return . f)

-- | Remove tagged variables in a monad.
--
-- The remove function is exectued only once for each tagged variable,
-- and a `Map` of renamings is returned.
--
-- This is useful if you want to sync it with your own name supply monad.
unTagMapM :: Monad m => (Tagged v -> m v') -> [TaggedObligation c v t]
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

