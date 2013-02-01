-- | Linearisation
{-# LANGUAGE RecordWildCards #-}
module Induction.Structural.Linearise
    (
    -- * Linearising (pretty-printing) obligations
      linObligation,
      Style(..),
      strStyle,
    -- ** Convenience re-export
      render
    ) where

import Induction.Structural.Types

import Text.PrettyPrint hiding (Style)

-- | Functions for linearising constructors (`linc`), variables (`linv`) and
-- types (`lint`).
data Style c v t = Style
    { linc :: c -> Doc
    , linv :: v -> Doc
    , lint :: t -> Doc
    }

-- | An example style where constructors, variables and types are represented as `String`.
strStyle :: Style String String String
strStyle = Style
    { linc = text
    , linv = text
    , lint = text
    }

-- | Linearises an `Obligation` in a certain `Style`.
linObligation :: Style c v t -> Obligation c v t -> Doc
linObligation Style{..} p = case p of
    Obligation sks []   concl -> linForall sks <+> linPred concl
    Obligation sks hyps concl -> hang (linForall sks) 4 $
        cat $ parList $
            punctuate (fluff ampersand) (map linHyp hyps) ++
            [space <> darrow <+> linPred concl]
  where
    linTerm tm = case tm of
        Var v    -> linv v
        Con c [] -> linc c
        Con c ts -> linc c <> parens (csv (map linTerm ts))
        Fun v ts -> linv v <> parens (csv (map linTerm ts))

    linTypedVar v t = linv v <+> colon <+> lint t

    linForall [] = empty
    linForall qs =
        bang <+> brackets (csv (map (uncurry linTypedVar) qs)) <+> colon

    linPred xs = char 'P' <> parens (csv (map linTerm xs))

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

