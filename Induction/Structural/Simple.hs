{-# LANGUAGE ParallelListComp, ScopedTypeVariables, TypeOperators #-}
module Induction.Structural.Unsound (structuralInductionUnsound) where

import Control.Arrow hiding ((<+>))
import Control.Applicative hiding (empty)
import Control.Monad.State

import Data.List
import Data.Maybe

import Induction.Structural.Auxiliary (concatFoldM)
import Induction.Structural.Types
import Induction.Structural.Utils

import Safe

type C c t = (c,[Arg t])

type Endo a = a -> a

-- | Gets all well-typed subterms of a term, including yourself.
--
-- The first argument is always yourself.
--
-- We need terms where the constructors are associated with their arguments.
subterms :: Term (C c t) v -> [Term (C c t) v]
subterms (Var x) = [Var x]
subterms (Fun x tms) = Fun x tms : Fun x (mapM subterms tms)
subterms (Con c@(_,as) tms) = direct ++ indirect
  where
    direct   = map (Con c) (mapM subterms tms)
    indirect = [ subterms tm | Rec _ <- as | tm <- tms ]

type QuantTerm c v t = ([V v ::: t],TermV (C c t) v t)

-- | Instantiate a variable with a given type, returning the new variables and
--   what the term should be replaced with
inst :: TyEnv c v t -> V v -> t -> Fresh (Maybe [QuantTerm c v t])
inst env v t tm = case env t of
    Just ks -> Just <$> mapM (uncurry inst') ks
    Nothing -> return Nothing
  where
    -- New variables and replacement term from a constructor and its arguments
    inst' :: c -> [Arg t] -> Fresh (QuantTerm c v t)
    inst' k as = do
        args <- mapM (refreshTypedV v . argRepr) as
        return (args,Con (k,as) (map Var args))

-- | Induction on a term.
inductionTm :: TyEnv c t -> QuantTerm c v t -> Fresh [QuantTerm c v t]
inductionTm env q@(xs,tm) = case tm of
    Var x -> do
        let ty = lookupJustNote "inductionTm: x not quantified" x xs
        m_q' <- inst env v ty
        -- Were we able to instantiate?
        return $ case m_q' of
            Just (xs',tm') -> (delete x (xs ++ xs'),tm')
            Nothing        -> q
    con_or_fun -> concatFoldM (inductionTm env) q (termArgs con_or_fun)

-- CONTINUE FROM HERE

-- | Gets the n:th argument of the conclusion, in the consequent
getNthArg :: Int -> IndPart c v t -> Term c v
getNthArg i p = atNote "Induction.getNthArg" (conclusion p) i

-- | Induction on the term on the n:th coordinate of the predicate.
inductionNth :: TyEnv c t -> IndPartV (C c t) v t -> Int -> Fresh [IndPartV (C c t) v t]
inductionNth ty_env phi i = inductionTm ty_env phi (getNthArg i phi)

-- | Unrolls to a given depth, but does not add any hypotheses
noHyps :: TyEnv c t -> [(v,t)] -> [Int] -> [IndPartV (C c t) v t]
noHyps env vars coords =

removeArgs :: [IndPart (C c t) v t] -> [IndPart c v t]
removeArgs parts =
    [ IndPart skolem [ (qs,map go hyp) | (qs,hyp) <- hyps ] (map go concl)
    | IndPart skolem hyps concl <- parts
    ]
  where
    go tm = case tm of
        Var x         -> Var x
        Con (c,_) tms -> Con c (map go tms)
        Fun f     tms -> Fun f (map go tms)

sillyInduction :: TyEnv c t -> [(v,t)] -> [Int] -> [IndPartV c v t]
sillyInduction env args coords = removeArgs (noHyps env args coords)

structuralInductionSubterms
    :: (Ord c,Ord v)
    => TyEnv c t
    -- ^ Constructor typed environment
    -> [(v,t)]
    -- ^ The initial arguments and types to P
    -> [Int]
    -- ^ The coordinates to do induction on in P, in order
    -> [IndPartV c v t]
    -- ^ The set of clauses to prove
structuralInductionSubterms ty_env args coords = flip evalState 0 $ do

    args_fresh <- mapM (uncurry newTyped) args

    let init_part = IndPart args_fresh [] (map (Var . fst) args_fresh)

    concatFoldM (inductionNth ty_env) init_part coordinates

