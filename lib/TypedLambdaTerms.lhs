\begin{code}

module TypedLambdaTerms where

import Lambda
import TypedLambda

-- Common lambda terms
λI :: Λ
λI = λ ("x" ::: "σ") --> "x"

-- Boolean values
λtrue, λfalse :: Λ
λtrue = λ ("x" ::: "σ") ("y" ::: "σ") --> "x"
λfalse = λ ("x" ::: "σ") ("y" ::: "σ") --> "y"

-- Conditionals with nice "inline" syntax:
-- "if P then Q else R" <==> {λif P ? Q |: R} <==> {P $$ Q $$ R}
λif :: Λ -> (Λ -> Λ -> Λ)
λif p q r = p $$ q $$ r

(?) :: (Λ -> Λ -> Λ) -> Λ -> (Λ -> Λ)
(?) p' = p'

(|:) :: (Λ -> Λ) -> Λ -> Λ
(|:) q' = q'

-- Pairs and two pair accessors
λpairType :: Type Λ
λpairType = "σ" ==> "σ" ==> "σ"

λpair :: Λ
λpair = λ ("x" ::: "σ") ("y" ::: "σ") ("f" ::: λpairType) --> "f" $$ "x" $$ "y"

λp1, λp2 :: Λ
λp1 = λ ("p" ::: λpairType ==> "σ") --> "p" $$ (λ ("x" ::: "σ") ("y" ::: "σ") --> "x")
λp2 = λ ("p" ::: λpairType ==> "σ") --> "p" $$ (λ ("x" ::: "σ") ("y" ::: "σ") --> "y")

\end{code}
