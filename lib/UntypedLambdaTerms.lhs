\subsection{Example Terms}
We implement some standard example terms in our untyped $λ$-calculus. These can be used for basic testing or exploration of the realms of $λ$-terms.

\begin{code}
module UntypedLambdaTerms where

import UntypedLambda

-- Common lambda terms
λI, λK, λS, λΩ, λY :: Λ
λI = λ"x" --> "x"
λK = λ"x" "y" --> "x"
λS = λ"x" "y" "z" --> "x" $$ "z" $$ ("y" $$ "z")
λΩ = let λω = λ "x" --> "x" $$ "x" in λω $$ λω
λY = λ "f" --> (λ "x" --> "f" $$ ("x" $$ "x")) $$ (λ "x" --> "f" $$ ("x" $$ "x"))
\end{code}
\vspace{-23pt}

Notably here, {\tt λΩ} is non-normalising and always reduces to itself. Similarly, {\tt λY} is non-normalising, but has an infinite reduction path to ever-different terms - it will never cycle back to itself. {\tt λK} and {\tt λS} correspond to combinators as they are defined in combinatory logic.

\begin{code}
-- Boolean values
λtrue, λfalse :: Λ
λtrue = λ "x" "y" --> "x"
λfalse = λ "x" "y" --> "y"

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
λpair = λ "x" "y" "f" --> "f" $$ "x" $$ "y"

λp1, λp2 :: Λ
λp1 = λ "p" --> "p" $$ (λ "x" "y" --> "x")
λp2 = λ "p" --> "p" $$ (λ "x" "y" --> "y")
\end{code}
\vspace{-23pt}

We implement standard booleans and some syntax to more easily do a ternary if-statement; but it essentially just concatenates the three terms. In addition, we implement pairs and two accessors/deconstructors.

\begin{code}
-- Church numerals and various arithmetical operations
church :: Int -> Λ
church 0 = λ "f" "x" --> "x"
church n = λ "f" "x" --> fs n
    where
        fs :: Int -> Λ
        fs 1 = "f" $$ "x"
        fs m = "f" $$ fs (m - 1)

λsucc, λadd, λmult, λexp, λzero :: Λ
λsucc = λ "n" "f" "x" --> "f" $$ ("n" $$ "f" $$ "x")
λadd = λ "m" "n" "f" "x" --> "m" $$ "f" $$ ("n" $$ "f" $$ "x")
λmult = λ "m" "n" "f" "x" --> "m" $$ ("n" $$ "f") $$ "x"
λexp = λ "m" "n" "f" "x" --> "m" $$ "n" $$ "f" $$ "x" -- "other way around": λexp a b <=> b^a
λzero = λ "m" --> church 0

-- λit has the property that:
---- λit x y (church 0) === x
---- λit x y (λsucc n) === y $$ (λit x y n)
λit :: Λ
λit = λ "x" "y" "z" --> "z" $$ "y" $$ "x"

-- λiszero has the property that:
---- λiszero (church 0) === λtrue
---- λiszero (λsucc n) === λfalse
λiszero :: Λ
λiszero = λit $$ λtrue $$ (λ"x" --> λfalse)

-- Predecessor function
λpred :: Λ
λpred = λ "x" --> λp1 $$ (λQ $$ "x")
    where λQ = λit $$ (λpair $$ church 0 $$ church 0) $$ (λ"x" --> (λpair $$ (λp2 $$ "x") $$ (λsucc $$ (λp2 $$ "x"))))
\end{code}
\vspace{-23pt}

Lastly, we implement Church numerals and various arithmetical operations in a canonical way. Only the predecessor is slightly different, taken from how it was introduced in the Type Theory course. These examples show the utility of the `parser' functions we implemented, and how they drastically help code clarity. At the same time, we keep the analysis from GHC to ensure our syntax is correct, so we don't run into issues at runtime when it turns out we wrote an incorrect $λ$-term.
