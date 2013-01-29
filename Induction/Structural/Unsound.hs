{-# LANGUAGE ParallelListComp, ScopedTypeVariables, TypeOperators #-}
module Induction.Structural.Unsound (structuralInductionUnsound) where

import Control.Arrow hiding ((<+>))
import Control.Applicative hiding (empty)

import Data.List
import Data.Maybe

import Induction.Structural.Auxiliary (concatFoldM)
import Induction.Structural.Types
import Induction.Structural.Utils

import Safe

{-  Induction

    Induction on a variable, given one constructor and the type of
    its arguments. We need to make some special care when
    we are doing induction on an implication. Say we have

    @
      ∀ (x,xs) . γ(xs) ∧ φ(x,xs) → ψ(x,xs)
    @

    The γ are properties unrelated to x. These are put away for now.
    We're doing induction on x, it has a constructor C with n
    arguments, let's for simplicitity say that they are all recursive.
    Now, define a temporary P:

    @
      P(x) <=> ∀ xs . φ(x,xs) ∧ ψ(x,xs)
    @

    Notice the conjuction. Induction:

    @
      ∀ (x₁..xₙ) . P(x₁) ∧ ... ∧ P(xₙ)
                 → P(C x₁ .. xₙ)
    @

    Unroll P, and move its quantifier in the consequent:

    @
      ∀ (x1..xn) xs . (∀ xs′ . φ(x₁,xs′) ∧ ψ(x₁,xs′))
                    ∧ ...
                    ∧ (∀ xs′ . φ(xₙ,xs′) ∧ ψ(xₙ,xs′))
                    → φ(C x₁ .. xₙ,xs) ∧ ψ(C x₁ .. xₙ,xs)
    @

    Ok, so we have two proof obligations, φ and ψ. Let us take φ
    first. It turns out that we don't need ψ here, so we strip them:

    @
      ∀ (x1..xn) xs . (∀ xs′ . φ(x₁,xs′))
                    ∧ ...
                    ∧ (∀ xs′ . φ(xₙ,xs′))
                    → φ(C x₁ .. xₙ,xs)
    @

    And this is true by structural induction! Hooray! So what we are
    left with is this:

    @
      ∀ (x1..xn) xs . (∀ xs′ . φ(x₁,xs′) ∧ ψ(x₁,xs′))
                    ∧ ...
                    ∧ (∀ xs′ . φ(xₙ,xs′) ∧ ψ(xₙ,xs′))
                    → ψ(C x₁ .. xₙ,xs)
    @

    Since our target language does not have conjuction, we may just as
    well write it as this:

    @
      ∀ (x1..xn) xs . (∀ xs′ . φ(x₁,xs′))
                    ∧ ...
                    ∧ (∀ xs′ . φ(xₙ,xs′))
                    ∧ (∀ xs′ . ψ(x₁,xs′))
                    ∧ ...
                    ∧ (∀ xs′ . ψ(xₙ,xs′))
                    → ψ(C x₁ .. xₙ,xs)
    @

    Now, we knew from the start that ∀ xs . γ(xs), se we bring that back:

    @
      ∀ (x1..xn) xs . γ(xs)
                    ∧ (∀ xs′ . φ(x₁,xs′))
                    ∧ ...
                    ∧ (∀ xs′ . φ(xₙ,xs′))
                    ∧ (∀ xs′ . ψ(x₁,xs′))
                    ∧ ...
                    ∧ (∀ xs′ . ψ(xₙ,xs′))
                    → ψ(C x₁ .. xₙ,xs)
    @

    Then it fits our data type perfectly. We have implicitly
    quantified variables, x1 .. xn and xs, a bunch of hypotheses
    quantifying new variables, and and induction conclusion.
-}
-- | Induction on a constructor, given its arguments as above
indCon :: forall c v t . (Ord c,Ord v)
       => IndPartV c v t -> V v -> c -> [Arg t] -> Fresh (IndPartV c v t)
indCon (IndPart x_and_xs gamma_and_phi psi) x con arg_types = do

   let phis :: [HypothesisV c v t]
       (phis,gamma) = partition (any (varFree x) . snd) gamma_and_phi

       xs = mdelete x x_and_xs

   xs' <- mapM (uncurry refreshTypedV) xs

   let (psi':phis') = map (second (map (substList [ (v,Var v')
                                                  | (v,_) <- xs
                                                  | (v',_) <- xs' ])))
                          (([],psi):phis)


   x1xn_args <- mapM (refreshTypedV x) arg_types

   let x1xn = map fst x1xn_args

   antecedents <- catMaybes <$> sequence
                      [ fmap (quantify xs')
                          <$> hypothesis (\tm -> (qs,map (subst x tm) hyp)) xi arg
                      | (xi,arg) <- x1xn_args
                      , (qs,hyp) <- psi':phis'
                      ]

   let consequent = map (substList [(x,Con con (map Var x1xn))]) psi

       x1xn_typed = map (second argRepr) x1xn_args

   return $ IndPart (x1xn_typed ++ xs)
                    (tidy $ gamma ++ antecedents)
                    consequent

{-
    In the commentary about indCon we assumed that all arguments were
    recurisive. This is not necessarily so, consider

    @
       (:) : a -> [a] -> [a]
    @

    The first argument is non-recursive, the second is recursive. We
    also have exponentials:

    @
       Lim : (Nat -> Ord) -> Ord
    @

    While while we cannot continue do induction on the function space
    Nat -> Ord, we still get an induction hypothesis:

    @
       ∀ f . (∀ x . P(f(x))) → P(Lim(f))
    @

    To summarise, given the constructor C t₁ .. tₙ and formula

    @
       ∀ (x,xs) . φ(x,xs) → ψ(x,xs)
    @

    yields, when doing induction on x:

    @
       ∀ (x₁:t₁ .. xₙ:tₙ,xs) .

         ⋀ { if tᵢ non-recursive : ∅
             if tᵢ recursive     : { ∀ xs′ . φ(xᵢ,xs′)
                                   , ∀ xs′ . ψ(xᵢ,xs′)
                                   }
             if tᵢ exponential,
             with arguments of type ts : { ∀ xs′ . ∀ (ys : ts) . φ(xᵢ(ys),xs′)
                                         , ∀ xs′ . ∀ (ys : ts) . ψ(xᵢ(ys),xs′)
                                         }
             as a function call on xᵢ with args ys
           | xᵢₖ <- x₁..xₙ
           }

         → ψ(C x₁..xₙ,xs)
    @
-}

-- | This function returns the hypothesis, given a φ(/x),
--      i.e a hypothesis waiting for a substiution
hypothesis :: (Ord c,Ord v)
           => (TermV c v -> HypothesisV c v t) -> V v -> Arg t
           -> Fresh (Maybe (HypothesisV c v t))
hypothesis phi_slash xi arg = case arg of
   NonRec _        -> return Nothing
   Rec _           -> return (Just (phi_slash (Var xi)))
   Exp _ arg_types -> do
       args_typed <- mapM (refreshTypedV xi) arg_types
       let phi = phi_slash (Fun xi (map (Var . fst) args_typed))
       return (Just (quantify args_typed phi))

-- | Induction on a variable, given all its constructors and their types
--
-- Returns a number of clauses to be proved, one for each constructor.
induction :: (Ord c,Ord v)
          => IndPartV c v t -> V v -> [c ::: [Arg t]] -> Fresh [IndPartV c v t]
induction phi x cons = sequence [ indCon phi x con arg_types
                                | (con,arg_types) <- cons ]

-- | Induction on a term.
--
-- When we have picked out an argument to the predicate P, it may just as well
-- be a constructor x : xs, and then we can do induction on x and xs
-- (possibly).
inductionTm :: (Ord c,Ord v)
            => TyEnv c t -> IndPartV c v t -> TermV c v -> Fresh [IndPartV c v t]
inductionTm ty_env part@(IndPart xs _ _) tm = case tm of
    Var x -> let ty = lookupJustNote "inductionTm: x not quantified" x xs
             in  case ty_env ty of
                     Just cons -> induction part x cons
                     Nothing   -> return [part]
    con_or_fun -> concatFoldM (inductionTm ty_env) part (termArgs con_or_fun)

-- | Gets the n:th argument of the conclusion, in the consequent
getNthArg :: Int -> IndPart c v t -> Term c v
getNthArg i p = atNote "Induction.getNthArg" (conclusion p) i

-- | Induction on the term on the n:th coordinate of the predicate.
inductionNth :: (Ord c,Ord v)
             => TyEnv c t -> IndPartV c v t -> Int -> Fresh [IndPartV c v t]
inductionNth ty_env phi i = inductionTm ty_env phi (getNthArg i phi)

-- | Perform repeated structural induction, given the typing environment
--
--  * the constructors and their Arg types, for any type
--
--  * arguments and their types
--
--  * which coordinates to do induction on, in order
structuralInductionUnsound
    :: (Ord c,Ord v)
    => TyEnv c t
    -- ^ Constructor typed environment
    -> [(v,t)]
    -- ^ The initial arguments and types to P
    -> [Int]
    -- ^ The coordinates to do induction on in P, in order
    -> [IndPartV c v t]
    -- ^ The set of clauses to prove
structuralInductionUnsound ty_env args coordinates = runFresh $ do

    args_fresh <- mapM (uncurry newTyped) args

    let init_part = IndPart args_fresh [] (map (Var . fst) args_fresh)

    concatFoldM (inductionNth ty_env) init_part coordinates

