{-# LANGUAGE GADTs, RankNTypes, TypeOperators, FlexibleInstances #-}
module Walk where

import Test.QuickCheck
import Data.List
import Control.Monad
import Control.Applicative

import Induction.Structural

import Trace
import EnvTypes
import Env
import Util

construct :: VarMap -> Hyp -> Gen [Repr']
construct vm (hyps,tms) = mapM (construct1 hyps vm) tms

construct1 :: [(String,Ty')] -> VarMap -> Tm -> Gen Repr'
construct1 hyps vm tm = case tm of
    Var s -> case lookup s vm of
        Just u  -> return u
        Nothing -> case lookup s hyps of
            Just t  -> arbFromType' t
            -- ^ if this is missing, generate a new one with arbitrary!!
            Nothing -> error $ show s ++ " missing!" ++ show vm ++ "," ++ show hyps
    Con s tms ->  mkCon s <$> mapM (construct1 hyps vm) tms
    Fun{} -> error "exponentials not supported"

-- | We can only pick 1-2 hyps, otherwise we get crazy exponential behaviour
pickHyps :: [a] -> Gen [a]
pickHyps [] = return []
pickHyps hs = do
    let n = length hs - 1
    i <- choose (0,n)
    i' <- choose (0,n)
    two <- arbitrary
    return $ if two && i /= i' then [hs !! i,hs !! i'] else [hs !! i]

-- TODO: Can this be reorganized so we get an efficient unrolling?
makeTracer :: [Repr'] -> [Oblig] -> Gen (Trace [Repr'])
makeTracer args parts = go parts
  where
    go p = case p of
        Obligation _ hyps conc:is
            | length args == length conc -> case zipWithM match args conc of
                Nothing -> go is
                Just vms -> halfSize $ \ _ -> do
                    -- Throw away some hypotheses
                    hyps' <- pickHyps hyps
                    argss' <- mapM (construct (concat vms)) hyps'
                    forks <- mapM (`makeTracer` parts) argss'
                    return (Fork args forks)
            | otherwise -> mk_error $ "Unequal lengths (conc=" ++
                intercalate "," (map (render . linTerm style) conc) ++ ")"
        _ -> mk_error "No case"
      where
        mk_error msg = error $
            "makeTracer " ++ show args ++ " : " ++ msg ++ "!" ++
            "\nDetails: args = (" ++ intercalate " , " (map showRepr' args) ++ ")" ++
            "\nCheck Env.match and EnvTypes.==?, or case is missing from schema:" ++
            "\n" ++ showOblig parts
