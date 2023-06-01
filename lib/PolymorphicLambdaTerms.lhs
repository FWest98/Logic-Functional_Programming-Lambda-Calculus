\begin{code}

module PolymorphicLambdaTerms where

import PolymorphicLambda

-- Boolean values
boolean :: PType
boolean = Forall "p" ("p" ==> "p" ==> "p")

true, false :: ΛP
true = lPT "p" --> lP ("x" ::: "p") ("y" ::: "p") --> "x"
false = lPT "p" --> lP ("x" ::: "p") ("y" ::: "p") --> "y"

neg, land :: ΛP
neg = lP ("u" ::: boolean) --> lPT "q" --> lP ("x" ::: "q") ("y" ::: "q") --> "u" $$ "q" $$ "y" $$ "x"
land = lP ("u" ::: boolean) ("v" ::: boolean) --> lPT "q" --> lP ("x" ::: "q") ("y" ::: "q")
        --> "u" $$ "q" $$ ("v" $$ "q" $$ "x" $$ "y") $$ ("v" $$ "q" $$ "y" $$ "y")

-- Trees (from the Type Theory exam)
tree :: PType
tree = Forall "p" ((boolean ==> "p") ==> (boolean ==> "p" ==> "p" ==> "p") ==> "p")

construct :: LambdaP -> LambdaP
construct form = lPT "p" --> lP ("leaf" ::: boolean ==> "p") ("node" ::: boolean ==> "p" ==> "p" ==> "p") --> form

join :: LambdaP
join = lP ("z" ::: boolean) ("x" ::: tree) ("y" ::: tree)
        --> lPT "p" --> lP ("leaf" ::: boolean ==> "p") ("node" ::: boolean ==> "p" ==> "p" ==> "p")
        --> "node" $$ "z" $$ ("x" $$ "p" $$ "leaf" $$ "node") $$ ("y" $$ "p" $$ "leaf" $$ "node")

falseNode, trueNode, simpleFork :: LambdaP
falseNode = construct $ "leaf" $$ false
trueNode = construct $ "leaf" $$ true
simpleFork = construct $ "node" $$ true $$ ("leaf" $$ false) $$ ("leaf" $$ true)

sampleJoin :: ΛP
sampleJoin = join $$ true $$ falseNode $$ trueNode

\end{code}


(λz:∀p.p->p->p,x:∀p.((∀p.p->p->p)->p)->((∀p.p->p->p)->p->p->p)->p,y:∀p.((∀p.p->p->p)->p)->((∀p.p->p->p)->p->p->p)->p.Λpλleaf:(∀p.p->p->p)->p,node:(∀p.p->p->p)->p->p->p.(node:(∀p.p->p->p)->p->p->p)(z:∀p.p->p->p)(x:p)(y:p))
z:(Λpλx:p,y:p.(x:p))
x:(Λpλleaf:(∀p.p->p->p)->p,node:(∀p.p->p->p)->p->p->p.(leaf:(∀p.p->p->p)->p)(Λpλx:p,y:p.(y:p)))
y:(Λpλleaf:(∀p.p->p->p)->p,node:(∀p.p->p->p)->p->p->p.(leaf:(∀p.p->p->p)->p)(Λpλx:p,y:p.(x:p)))

(λx:∀p.((∀p.p->p->p)->p)->((∀p.p->p->p)->p->p->p)->p,y:∀p.((∀p.p->p->p)->p)->((∀p.p->p->p)->p->p->p)->p.Λpλleaf:(∀p.p->p->p)->p,node:(∀p.p->p->p)->p->p->p.(node:(∀p.p->p->p)->p->p->p)(Λpλx:p,y:p.(x:p))(x:p)(y:p))
(Λpλleaf:(∀p.p->p->p)->p,node:(∀p.p->p->p)->p->p->p.(leaf:(∀p.p->p->p)->p)(Λpλx:p,y:p.(y:p)))
(Λpλleaf:(∀p.p->p->p)->p,node:(∀p.p->p->p)->p->p->p.(leaf:(∀p.p->p->p)->p)(Λpλx:p,y:p.(x:p)))

Λpλleaf:(∀p.p->p->p)->p,node:(∀p.p->p->p)->p->p->p.
(node:(∀p.p->p->p)->p->p->p)
(Λpλx:p,y:p.(x:p))
((λleaf:(∀p.p->p->p)->p,node:(∀p.p->p->p)->p->p->p.(leaf:(∀p.p->p->p)->p)(Λpλx:p,y:p.(y:p)))(leaf:(∀p.p->p->p)->p)(node:(∀p.p->p->p)->p->p->p))
((λleaf:(∀p.p->p->p)->p,node:(∀p.p->p->p)->p->p->p.(leaf:(∀p.p->p->p)->p)(Λpλx:p,y:p.(x:p)))(leaf:(∀p.p->p->p)->p)(node:(∀p.p->p->p)->p->p->p))
