\begin{code}

module Main where

import Lambda
import UntypedLambda
import Data.Set

import Test.Hspec

-- Testing data
expr :: Λ
expr = (λ"x" --> "x") $$ "y"

main :: IO ()
main = hspec $ do
    describe "Lambdas" $ do
        it "correct free variables" $
            freeVariables expr `shouldBe` singleton "y"
        it "substitution" $
            substitute expr "x" (fromVarName "y") `shouldBe` Just expr
        it "sub2" $
            substitute expr "y" (fromVarName "x") `shouldNotBe` Just expr
        it "αEquiv" $
            ((λ"x" "z" --> "x" $$ "z") == (λ"y" "z" --> "y" $$ "z")) `shouldBe` True

-- test ideas
-- substitution of variable to variable should not be alpha equivalent unless same variable
-- Lemma 1.2.10: a equivalence has same free variables

\end{code}
