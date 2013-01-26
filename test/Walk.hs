{-# LANGUAGE GADTs, RankNTypes, TypeOperators, FlexibleInstances #-}
module Walk where

import Test.QuickCheck
import Control.Monad
import Control.Applicative
import Control.Parallel.Strategies

import Induction.Structural

import Trace
import EnvTypes
import Env
import Util

construct :: [VarMap] -> Hyp -> Gen [Repr']
construct vms (types,tms) = zipWithM (construct1 types) vms tms

construct1 :: [String ::: Ty'] -> VarMap -> Tm -> Gen Repr'
construct1 types vm tm = case tm of
    Var s -> case lookup s vm of
        Just u  -> return u
        Nothing -> case lookup s types of
            Just t  -> arbFromType' t
            -- ^ if this is missing, generate a new one with arbitrary!!
            Nothing -> error $ show s ++ " missing!" ++ show vm ++ "," ++ show types
    Con s tms ->  mkCon s <$> mapM (construct1 types vm) tms
    Fun{} -> error "exponentials not supported"

startFromTypes :: [Ty'] -> Gen [Repr']
startFromTypes = mapM arbFromType'

-- TODO: Can this be reorganized so we get an efficient unrolling?
makeTracer :: [Exists Repr] -> [IndP] -> Gen (Trace [Exists Repr])
makeTracer args parts = go parts
  where
    go [] = error $ "No case for " ++ show args
    go (IndPart _ hyps conc:is) = case zipWithM match args conc of
        Nothing -> go is
        Just vms -> halfSize $ \ _ -> do
            argss' <- mapM (construct vms) hyps
            forks <- mapM (`makeTracer` parts) argss'
            return (Fork args (forks `using` rpar))

