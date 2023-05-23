\begin{code}

{-

Some commonly-used lambda terms for various applications, this
serves as a small library to simplify testing and working with
the lambda calculus implemented in this library.

-}

module LambdaTerms where

import Lambda

-- Common lambda terms
λI, λK, λS, λΩ, λY :: Λ
λI = λ "x" --> v"x"
λK = λ "x" # "y" --> v"x"
λS = λ "x" # "y" # "z" --> v"x" $$ v"z" $$ (v"y" $$ v"z")
λΩ = let λω = λ "x" --> v"x" $$ v"x" in λω $$ λω
λY = λ "f" --> (λ "x" --> v"f" $$ (v"x" $$ v"x")) $$ (λ "x" --> v"f" $$ (v"x" $$ v"x"))

-- Boolean values
λtrue, λfalse :: Λ
λtrue = λ "x" # "y" --> v"x"
λfalse = λ "x" # "y" --> v"y"

-- Conditionals with nice "inline" syntax:
-- "if P then Q else R" <==> {λif P ? Q |: R} <==> {P $$ Q $$ R}
λif :: Λ -> (Λ -> Λ -> Λ)
λif p q r = p $$ q $$ r

(?) :: (Λ -> Λ -> Λ) -> Λ -> (Λ -> Λ)
(?) p' = p'

(|:) :: (Λ -> Λ) -> Λ -> Λ
(|:) q' = q'

-- Pairs and two pair accessors
λpair :: Λ
λpair = λ "x" --> v"x"

λp1, λp2 :: Λ
λp1 = λ "p" --> v"p" $$ (λ "x" # "y" --> v"x")
λp2 = λ "p" --> v"p" $$ (λ "x" # "y" --> v"y")

-- Church numerals and various arithmetical operations
church :: Int -> Λ
church 0 = λ "f" # "x" --> v"x"
church n = λ "f" # "x" --> fs n
  where
    fs :: Int -> Λ
    fs 1 = v"f" $$ v"x"
    fs m = v"f" $$ fs (m - 1)

λsucc, λadd, λmult, λexp, λzero :: Λ
λsucc = λ "n" # "f" # "x" --> v"f" $$ (v"n" $$ v"f" $$ v"x")
λadd = λ "m" # "n" # "f" # "x" --> v"m" $$ v"f" $$ (v"n" $$ v"f" $$ v"x")
λmult = λ "m" # "n" # "f" # "x" --> v"m" $$ (v"n" $$ v"f") $$ v"x"
λexp = λ "m" # "n" # "f" # "x" --> v"m" $$ v"n" $$ v"f" $$ v"x" -- "other way around": λexp a b <=> b^a
λzero = λ "m" --> church 0

-- λit has the property that:
---- λit x y (church 0) === x
---- λit x y (λsucc n) === y $$ (λit x y n)
λit :: Λ
λit = λ "x" # "y" # "z" --> v"z" $$ v"y" $$ v"x"

-- λiszero has the property that:
---- λiszero (church 0) === λtrue
---- λiszero (λsucc n) === λfasle
λiszero :: Λ
λiszero = λit $$ λtrue $$ (λ"x" --> λfalse)

-- Predecessor function
λpred :: Λ
λpred = λ "x" --> λp1 $$ (λQ $$ v"x")
  where λQ = λit $$ (λpair $$ church 0 $$ church 0) $$ (λ"x" --> (λpair $$ (λp2 $$ v"x") $$ (λsucc $$ (λp2 $$ v"x"))))

\end{code}
