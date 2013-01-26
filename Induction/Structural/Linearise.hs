{-# LANGUAGE TypeOperators, RecordWildCards, ScopedTypeVariables #-}
{-|

   Linearises the parts defined in HipSpec.Induction.

-}
module Induction.Structural.Linearise
    (Style(..), strStyle, linPart) where

import Induction.Structural

import Text.PrettyPrint hiding (Style)

data Style c v t = Style
    { linc :: c -> Doc
    , linv :: v -> Doc
    , lint :: t -> Doc
    }

strStyle :: Style String String String
strStyle = Style
    { linc = text
    , linv = text
    , lint = text
    }

linPart :: forall c v t . Style c v t -> IndPart c v t -> Doc
linPart Style{..} p = case p of
    IndPart sks []   concl -> linForall sks <+> linPred concl
    IndPart sks hyps concl -> hang (linForall sks) 4 $
        cat $ parList $
            punctuate (fluff ampersand) (map linHyp hyps) ++
            [space <> darrow <+> linPred concl]
  where
    linTerm :: Term c v -> Doc
    linTerm tm = case tm of
        Var v    -> linv v
        Con c [] -> linc c
        Con c ts -> linc c <> parens (csv (map linTerm ts))
        Fun v ts -> linv v <> parens (csv (map linTerm ts))

    linTypedVar :: v -> t -> Doc
    linTypedVar v t = linv v <+> colon <+> lint t

    linForall :: [v ::: t] -> Doc
    linForall [] = empty
    linForall qs =
        bang <+> brackets (csv (map (uncurry linTypedVar) qs)) <+> colon

    linPred :: [Term c v] -> Doc
    linPred xs = char 'P' <> parens (csv (map linTerm xs))

    linHyp :: Hypothesis c v t -> Doc
    linHyp ([],hyp) = linPred hyp
    linHyp (qs,hyp) = parens (linForall qs <+> linPred hyp)

csv :: [Doc] -> Doc
csv = hcat . punctuate comma

parList :: [Doc] -> [Doc]
parList []     = [parens empty]
parList [x]    = [x]
parList (x:xs) = (lparen <> x) : init xs ++ [last xs <> rparen]

ampersand :: Doc
ampersand = char '&'

bang :: Doc
bang = char '!'

fluff :: Doc -> Doc
fluff d = space <> d <> space

darrow :: Doc
darrow = text "=>"
