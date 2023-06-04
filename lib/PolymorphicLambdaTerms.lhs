\begin{code}

module PolymorphicLambdaTerms where

import Lambda
import PolymorphicLambda

-- Boolean values
boolean :: Type Λ
boolean = Forall "p" ("p" ==> "p" ==> "p")

true, false :: Λ
true = lT "p" --> l ("x" ::: "p") ("y" ::: "p") --> "x"
false = lT "p" --> l ("x" ::: "p") ("y" ::: "p") --> "y"

neg, land :: Λ
neg = l ("u" ::: boolean) --> lT "q" --> l ("x" ::: "q") ("y" ::: "q") --> "u" $$ "q" $$ "y" $$ "x"
land = l ("u" ::: boolean) ("v" ::: boolean) --> lT "q" --> l ("x" ::: "q") ("y" ::: "q")
        --> "u" $$ "q" $$ ("v" $$ "q" $$ "x" $$ "y") $$ ("v" $$ "q" $$ "y" $$ "y")

-- Trees (from the Type Theory exam)
tree :: Type Λ
tree = Forall "p" ((boolean ==> "p") ==> (boolean ==> "p" ==> "p" ==> "p") ==> "p")

construct :: Λ -> Λ
construct form = lT "p" --> l ("leaf" ::: boolean ==> "p") ("node" ::: boolean ==> "p" ==> "p" ==> "p") --> form

join :: Λ
join = l ("z" ::: boolean) ("x" ::: tree) ("y" ::: tree)
        --> lT "p" --> l ("leaf" ::: boolean ==> "p") ("node" ::: boolean ==> "p" ==> "p" ==> "p")
        --> "node" $$ "z" $$ ("x" $$ "p" $$ "leaf" $$ "node") $$ ("y" $$ "p" $$ "leaf" $$ "node")

falseNode, trueNode, simpleFork :: Λ
falseNode = construct $ "leaf" $$ false
trueNode = construct $ "leaf" $$ true
simpleFork = construct $ "node" $$ true $$ ("leaf" $$ false) $$ ("leaf" $$ true)

sampleJoin :: Λ
sampleJoin = join $$ true $$ falseNode $$ trueNode

\end{code}
