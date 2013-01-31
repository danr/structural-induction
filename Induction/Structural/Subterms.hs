-- | Induction with subterms as hypotheses
{-# LANGUAGE ParallelListComp, ScopedTypeVariables, TypeOperators #-}
module Induction.Structural.Subterms
    (
    -- * Induction with subterms as hypotheses
      subtermInductionQ,
      subtermInduction,
    -- * Case analysis (no induction hypotheses)
      caseAnalysis
    ) where

import Control.Applicative
import Control.Arrow (first)
import Control.Monad.State

import Data.Maybe

import Induction.Structural.Auxiliary (concatMapM)
import Induction.Structural.Types
import Induction.Structural.Utils

import Safe

-- We annotate constructors in the terms with the types of the arguments they
-- have to easily be able to calculate subterms
type C c t = (c,[Arg t])

-- Term and terms explicitly quantified with variables
type QuantTerm c v t = ([(Tagged v,t)],TermTagged (C c t) v)
type QuantTerms c v t = ([(Tagged v,t)],[TermTagged (C c t) v])

-- Given
--
--      [ [ all x0 . P (tx0) , all x1 . P(tx1) ]
--      , [ all y0 . P (ty0) , all y1 . P(ty1) ]
--      ]
--
-- Returns
--
--      [ all x0 y0 . P (tx0,ty0)
--      , all x0 y1 . P (tx0,ty1)
--      , all x1 y0 . P (tx1,ty0)
--      , all x1 y1 . P (tx1,ty1)
--      ]
--
-- Assumption: x0, x1, y0, y1 are all different
makeQuantTerms :: [[QuantTerm c v t]] -> [QuantTerms c v t]
makeQuantTerms qtmss =
    [ (concat qs,tms)
    | qtms <- sequence qtmss
    , let (qs,tms) = unzip qtms
    ]

-- | Instantiate a variable with a given type, returning the new variables and
--   what the term should be replaced with
inst :: forall c v t . TyEnv c t -> Tagged v -> t -> Fresh (Maybe [QuantTerm c v t])
inst env v t = case env t of
    Just ks -> Just <$> mapM (uncurry inst') ks
    Nothing -> return Nothing
  where
    inst' :: c -> [Arg t] -> Fresh (QuantTerm c v t)
    inst' k as = do
        args <- mapM (refreshTypedTagged v . argRepr) as
        return (args,Con (k,as) [ Var x | (x,_) <- args ])

-- | Induction on every variable in a term
--
-- Assumption: The variables only occur once in each term.
inductionTm :: forall c v t .
               TyEnv c t -> QuantTerm c v t -> Fresh [QuantTerm c v t]
inductionTm env (qs0,tm0) = go tm0
  where
    go :: TermTagged (C c t) v -> Fresh [QuantTerm c v t]
    go tm = case tm of
        Var x@(_,x_idx) -> do
            let ty = headNote "inductionTm: unbound variable!"
                     [ t | ((_,idx),t) <- qs0, x_idx == idx ]
            fromMaybe [([(x,ty)],tm)] <$> inst env x ty
        Con c tms -> goTms (Con c) tms
        Fun f tms -> goTms (Fun f) tms

    goTms :: ([TermTagged (C c t) v] -> TermTagged (C c t) v) ->
             [TermTagged (C c t) v] -> Fresh [QuantTerm c v t]
    goTms mk tms0 = do
        qtmss <- mapM go tms0
        return [ (qs,mk tms) | (qs,tms) <- makeQuantTerms qtmss ]

-- | Induction several times on a variable
repeatInductionTm :: forall c v t . TyEnv c t -> v -> t -> Int -> Fresh [QuantTerm c v t]
repeatInductionTm env v t n0 = do
    vv <- newTyped v t
    go n0 [([vv],Var (fst vv))]
  where
    go :: Int -> [QuantTerm c v t] -> Fresh [QuantTerm c v t]
    go 0 qtms = return qtms
    go n qtms = concatMapM (go (n - 1) <=< inductionTm env) qtms

-- | Unroll to a given depth, but does not add any hypotheses
noHyps :: forall c v t . TyEnv c t -> [(v,t)] -> [Int]
       -> Fresh [ObligationTagged (C c t) v t]
noHyps env vars coords = do
    obligs <- sequence
        [ repeatInductionTm env v t (length (filter (ix ==) coords))
        | (v,t) <- vars
        | ix <- [0..]
        ]
    return $ makeObligations (makeQuantTerms obligs)

-- | Make Obligations: this means to add empty hypotheses to QuantTerms.
makeObligations :: [QuantTerms c v t] -> [ObligationTagged (C c t) v t]
makeObligations qtms = [ Obligation qs [] tms | (qs,tms) <- qtms ]

-- | Removes the argument type information from the constructors
removeArgs :: [Obligation (C c t) v t] -> [Obligation c v t]
removeArgs parts =
    [ Obligation skolem [ (qs,map go hyp) | (qs,hyp) <- hyps ] (map go concl)
    | Obligation skolem hyps concl <- parts
    ]
  where
    go tm = case tm of
        Var x         -> Var x
        Con (c,_) tms -> Con c (map go tms)
        Fun f     tms -> Fun f (map go tms)

-- | Does case analysis on a list of typed variables. No hypotheses.
--
-- subtermInduction is eactly this, but we add the subterms as hypotheses.
caseAnalysis :: TyEnv c t -> [(v,t)] -> [Int] -> [ObligationTagged c v t]
caseAnalysis env args = removeArgs . runFresh . noHyps env args

-- | Gets all well-typed subterms of a term, including yourself.
--
-- The first argument is always yourself.
--
-- We need terms where the constructors are associated with their arguments.
subterms :: Term (C c t) v -> [Term (C c t) v]
subterms (Var x) = [Var x]
subterms (Fun x tms) = Fun x tms : map (Fun x) (mapM subterms tms)
subterms (Con c@(_,as) tms) = direct ++ indirect
  where
    -- Starting with this constructor. This includes the term we started with.
    direct   = map (Con c) (mapM subterms tms)
    -- Well-typed subterms of the arguments to the constructor
    indirect = concat [ subterms tm | (Rec _,tm) <- zip as tms ]

-- | Adds hypotheses to an Obligation.
--
-- Important to drop 1, otherwise we get the conclusion as a hypothesis!
addHypotheses :: Obligation (C c t) v t -> Obligation (C c t) v t
addHypotheses (Obligation qs _ tms) = Obligation qs hyps tms
  where
    -- The empty lists denotes that we are not quantifying over any new
    -- variables in the hypotheses.
    hyps = [ ([],h) | h <- drop 1 (mapM subterms tms) ]

-- | Subterm induction
subtermInduction :: TyEnv c t -> [(v,t)] -> [Int] -> [ObligationTagged c v t]
subtermInduction env args =
    removeArgs . map addHypotheses . runFresh . noHyps env args

-- | Adds hypotheses to an Obligation, requantifying over naked variables
--
-- I.e. forall x y . P(K x,y) becomes
--      forall x y . (forall y'.P(x,y')) -> P (K x,y)
--
-- Important to drop 1, otherwise we get the conclusion as a hypothesis!
addHypothesesQ :: ObligationTagged (C c t) v t -> Fresh (ObligationTagged (C c t) v t)
addHypothesesQ ip = do -- Obligation qs hyps tms

    let Obligation qs hyps conc = addHypotheses ip

        mk_msg = ("addHypothesesQ: " ++)
        msg_unbound  = mk_msg "Unbound variable!"
        msg_mismatch = mk_msg "Concrete hypotheses but abstract conclusion!"

        -- tm is from a hypothesis, e from the conclusion.
        -- If e is a variable, tm should be the same, and we requantify over it
        addQ tm e = case e of
            Var x@(_,xi) -> case tm of
                Var (_,yi)
                    | xi == yi -> do
                        let t = mfindVNote msg_unbound x qs
                        xt'@(x',_) <- refreshTypedTagged x t
                        return ([xt'],Var x')
                _ -> error msg_mismatch
            _ -> return ([],tm)

    hyps' <- forM hyps $ \ ([],tms) -> mapAndUnzipM (uncurry addQ) (zip tms conc)

    return (Obligation qs (map (first concat) hyps') conc)

-- | Subterm induction
subtermInductionQ :: TyEnv c t -> [(v,t)] -> [Int] -> [ObligationTagged c v t]
subtermInductionQ env args =
    removeArgs . runFresh . (mapM addHypothesesQ <=< noHyps env args)

