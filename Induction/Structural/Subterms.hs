{-# LANGUAGE ParallelListComp, ScopedTypeVariables, TypeOperators #-}
module Induction.Structural.Subterms (sillyInduction) where

import Control.Applicative hiding (empty)
import Control.Monad.State

import Data.Maybe

import Induction.Structural.Auxiliary (concatMapM)
import Induction.Structural.Types
import Induction.Structural.Utils

import Safe

type C c t = (c,[Arg t])

-- | Gets all well-typed subterms of a term, including yourself.
--
-- The first argument is always yourself.
--
-- We need terms where the constructors are associated with their arguments.
subterms :: Term (C c t) v -> [Term (C c t) v]
subterms (Var x) = [Var x]
subterms (Fun x tms) = Fun x tms : map (Fun x) (mapM subterms tms)
subterms (Con c@(_,as) tms) = direct ++ concat indirect
  where
    direct   = map (Con c) (mapM subterms tms)
    indirect = [ subterms tm | Rec _ <- as | tm <- tms ]

type QuantTerm c v t = ([V v ::: t],TermV (C c t) v)
type QuantTerms c v t = ([V v ::: t],[TermV (C c t) v])

-- | Instantiate a variable with a given type, returning the new variables and
--   what the term should be replaced with
inst :: forall c v t . TyEnv c t -> V v -> t -> Fresh (Maybe [QuantTerm c v t])
inst env v t = case env t of
    Just ks -> Just <$> mapM (uncurry inst') ks
    Nothing -> return Nothing
  where
    inst' :: c -> [Arg t] -> Fresh (QuantTerm c v t)
    inst' k as = do
        args <- mapM (refreshTypedV v . argRepr) as
        return (args,Con (k,as) [ Var x | (x,_) <- args ])

-- | Induction on every variable in a term
inductionTm :: forall c v t . TyEnv c t -> QuantTerm c v t -> Fresh [QuantTerm c v t]
inductionTm env (qs0,tm0) = go tm0
  where
    go :: TermV (C c t) v -> Fresh [QuantTerm c v t]
    go tm = case tm of
        Var x@(_,x_idx) -> do
            let ty = headNote "inductionTm: unbound variable!" $
                     [ t | ((_,idx),t) <- qs0, x_idx == idx ]
            fromMaybe [([(x,ty)],tm)] <$> inst env x ty
        Con c tms -> goTms (Con c) tms
        Fun f tms -> goTms (Fun f) tms

    goTms :: ([TermV (C c t) v] -> TermV (C c t) v) ->
             [TermV (C c t) v] -> Fresh [QuantTerm c v t]
    goTms mk tms0 = do
        qtmss <- mapM go tms0
        return [ (qs,mk tms) | (qs,tms) <- makeQuantTerms qtmss ]

repeatInductionTm :: forall c v t . TyEnv c t -> v -> t -> Int -> Fresh [QuantTerm c v t]
repeatInductionTm env v t n0 = do
    vv <- newTyped v t
    go n0 [([vv],Var (fst vv))]
  where
    go :: Int -> [QuantTerm c v t] -> Fresh [QuantTerm c v t]
    go 0 qtms = return qtms
    go n qtms = concatMapM (go (n - 1) <=< inductionTm env) qtms

-- | Removes the argument type information from the constructors
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

-- | Unrolls to a given depth, but does not add any hypotheses
noHyps :: forall c v t . TyEnv c t -> [(v,t)] -> [Int]
       -> Fresh [IndPartV (C c t) v t]
noHyps env vars coords = do
    obligs <- sequence
        [ repeatInductionTm env v t (length (filter (ix ==) coords))
        | (v,t) <- vars
        | ix <- [0..]
        ]
    return $ makeIndParts (makeQuantTerms obligs)

makeQuantTerms :: [[QuantTerm c v t]] -> [QuantTerms c v t]
makeQuantTerms qtmss =
    [ (concat qs,tms)
    | qtms <- sequence qtmss
    , let (qs,tms) = unzip qtms
    ]

makeIndParts :: [QuantTerms c v t] -> [IndPartV (C c t) v t]
makeIndParts qtms = [ IndPart qs [] tms | (qs,tms) <- qtms ]

sillyInduction :: TyEnv c t -> [(v,t)] -> [Int] -> [IndPartV c v t]
sillyInduction env args = removeArgs . runFresh . noHyps env args

{-
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
structuralInductionSubterms ty_env args coords = runFresh $ do

    args_fresh <- mapM (uncurry newTyped) args

    let init_part = IndPart args_fresh [] (map (Var . fst) args_fresh)

    concatFoldM (inductionNth ty_env) init_part coordinates
-}
