{-# LANGUAGE GADTs, RankNTypes, TypeOperators, FlexibleInstances #-}
module Walk where

import Test.QuickCheck
import Data.List
import Control.Monad
import Control.Applicative
import Control.Parallel.Strategies
import Control.Exception.Base

import Induction.Structural

import Trace
import EnvTypes
import Env
import Util

construct :: VarMap -> Hyp -> Gen [Repr']
construct vm (hyps,tms) = mapM (construct1 hyps vm) tms

construct1 :: [String ::: Ty'] -> VarMap -> Tm -> Gen Repr'
construct1 hyps vm tm = case tm of
    Var s -> case lookup s vm of
        Just u  -> return u
        Nothing -> case lookup s hyps of
            Just t  -> arbFromType' t
            -- ^ if this is missing, generate a new one with arbitrary!!
            Nothing -> error $ show s ++ " missing!" ++ show vm ++ "," ++ show hyps
    Con s tms ->  mkCon s <$> mapM (construct1 hyps vm) tms
    Fun{} -> error "exponentials not supported"

-- TODO: Can this be reorganized so we get an efficient unrolling?
makeTracer :: [Repr'] -> [IndP] -> Gen (Trace [Repr'])
makeTracer args parts = go parts
  where
    go p = case p of
        IndPart _ hyps conc:is
            | length args == length conc -> case zipWithM match args conc of
                Nothing -> go is
                Just vms -> halfSize $ \ _ -> do
                    argss' <- mapM (construct (concat vms)) hyps
                    forks <- mapM (`makeTracer` parts) argss'
                    return (Fork args (forks `using` rpar))
            | otherwise -> mk_error $ "Unequal lengths (conc=" ++ show conc ++ ")"
        _ -> mk_error "No case"
      where
        mk_error msg = error $
            "makeTracer " ++ show args ++ " : " ++ msg ++ "!" ++
            "\nDetails: args = (" ++ intercalate " , " (map showRepr' args) ++ ")" ++
            "\nCheck Env.match and EnvTypes.==?, or case is missing from schema"
