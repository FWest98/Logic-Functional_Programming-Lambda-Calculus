\subsection{Example Terms}

Once more, we show some example terms in polymorphic $λ$-calculus that highlight the strength of the polymorphic aspect and our developer-friendly syntax. We can easily store types in variables, to make type signatures easier to read, and this allows us to create comprehensive and short expressions.

\begin{code}
module PolymorphicLambdaTerms where

import Lambda
import PolymorphicLambda

-- Boolean values
λboolean :: Type Λ
λboolean = Forall "p" ("p" ==> "p" ==> "p")

λtrue, λfalse :: Λ
λtrue = lT "p" --> l ("x" ::: "p") ("y" ::: "p") --> "x"
λfalse = lT "p" --> l ("x" ::: "p") ("y" ::: "p") --> "y"

λneg, λland :: Λ
λneg = l ("u" ::: λboolean) --> lT "q" --> l ("x" ::: "q") ("y" ::: "q") --> "u" $$ "q" $$ "y" $$ "x"
λland = l ("u" ::: λboolean) ("v" ::: λboolean) --> lT "q" --> l ("x" ::: "q") ("y" ::: "q")
        --> "u" $$ "q" $$ ("v" $$ "q" $$ "x" $$ "y") $$ ("v" $$ "q" $$ "y" $$ "y")
\end{code}
\vspace{-23pt}

In addition to the standard boolean values, we have defined negation and logical and operations.

\begin{code}
-- Trees (from the Type Theory exam)
λtree :: Type Λ
λtree = Forall "p" ((λboolean ==> "p") ==> (λboolean ==> "p" ==> "p" ==> "p") ==> "p")

λconstruct :: Λ -> Λ
λconstruct form = lT "p" --> l ("leaf" ::: λboolean ==> "p") ("node" ::: λboolean ==> "p" ==> "p" ==> "p") --> form

λjoin :: Λ
λjoin = l ("z" ::: λboolean) ("x" ::: λtree) ("y" ::: λtree)
        --> lT "p" --> l ("leaf" ::: λboolean ==> "p") ("node" ::: λboolean ==> "p" ==> "p" ==> "p")
        --> "node" $$ "z" $$ ("x" $$ "p" $$ "leaf" $$ "node") $$ ("y" $$ "p" $$ "leaf" $$ "node")

λfalseNode, λtrueNode, λsimpleFork :: Λ
λfalseNode = λconstruct $ "leaf" $$ λfalse
λtrueNode = λconstruct $ "leaf" $$ λtrue
λsimpleFork = λconstruct $ "node" $$ λtrue $$ ("leaf" $$ λfalse) $$ ("leaf" $$ λtrue)

λsampleJoin :: Λ
λsampleJoin = λjoin $$ λtrue $$ λfalseNode $$ λtrueNode
\end{code}
\vspace{-23pt}
