{- |

This package aims to perform the fiddly details of instantiating induction
schemas for algebraic data types. The library is parameterised over
the type of variables (@v@), constructors (@c@) and types (@t@).

Let's see how it looks if you instantiate all these three with String and want
to do induction over natural numbers. First, one needs to create a type
environment, a `TyEnv`. For every type (we only have one), we need to list its
constructors. For each constructor, we need to list its arguments and whether
they are recursive or not.

>testEnv :: TyEnv String String
>testEnv "Nat" = Just [ ("zero",[]) , ("succ",[Rec "Nat"]) ]
>testEnv _ = Nothing

Now, we can use the `subtermInduction` to get induction hypotheses which are
just subterms of the conclusion. Normally, you would translate the `Term`s from
the proof `Obligation`s to some other representation, but there is also
linearisation functions included (`linObligations`, for instance.)

>natInd :: [String] -> [Int] -> IO ()
>natInd vars coords = putStrLn
>    $ render
>    $ linObligations strStyle
>    $ unTag (\(x :~ i) -> x ++ show i)
>    $ subtermInduction testEnv typed_vars coords
>  where
>    typed_vars = zip vars (repeat "Nat")

The library will create fresh variables for you (called `Tagged` variables),
but you need to remove them, using for instance `unTag`. If you want to sync
it with your own name supply, use `unTagM` or `unTagMapM`.

An example invocation:

>*Mini> natInd ["X"] [0]
>P(zero).
>! [X1 : Nat] : (P(X1) => P(succ(X1))).

This means to do induction on the zeroth coord (hence the @0@), and the variable
is called "X". When using the library, it is up to you to translate the
abstract @P@ predicate to something meaningful.

We can also do induction on several variables:

>*Mini> natInd ["X","Y"] [0,1]
>P(zero,zero).
>! [Y3 : Nat] : (P(zero,Y3) => P(zero,succ(Y3))).
>! [X1 : Nat] : (P(X1,zero) => P(succ(X1),zero)).
>! [X1 : Nat,Y3 : Nat] :
>    (P(X1,Y3) &
>    P(X1,succ(Y3)) &
>    P(succ(X1),Y3)
>     => P(succ(X1),succ(Y3))).

In the last step case, all proper subterms of @succ(X1),succ(Y3)@ are used as
hypotheses.

A bigger example is in @example/Example.hs@ in the distribution.

-}
module Induction.Structural (
    module Induction.Structural.Subterms,
    module Induction.Structural.Types,
    module Induction.Structural.Linearise
) where

import Induction.Structural.Subterms
import Induction.Structural.Types
import Induction.Structural.Linearise

{-# ANN module "HLint: ignore Use import/export shortcut" #-}
