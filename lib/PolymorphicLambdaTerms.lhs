\begin{code}

module PolymorphicLambdaTerms where

import PolymorphicLambda

-- Boolean values
boolean :: PType
boolean = Forall "p" ("p" ==> "p" ==> "p")

true, false :: ΛP
true = lPT "p" --> lP ("x" ::: "p") ("y" ::: "p") --> "x"
false = lPT "p" --> lP ("x" ::: "p") ("y" ::: "p") --> "y"

neg :: ΛP
neg = lP ("u" ::: boolean) --> lPT "q" --> lP ("x" ::: "q") ("y" ::: "q") --> "u" $$ "q" $$ "y" $$ "x"

\end{code}
