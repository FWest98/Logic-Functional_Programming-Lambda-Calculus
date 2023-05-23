\begin{code}

module Main where

import Lambda
import Data.Set

import Test.Hspec
import Test.QuickCheck

-- Testing data
expr :: Λ
expr = (λ"x" --> v"x") $$ v"y"

main :: IO ()
main = hspec $ do
    describe "Lambdas" $ do
        it "correct free variables" $
            freeVariables expr `shouldBe` singleton "y"
        it "substitution" $
            substitute expr "x" (v"y") `shouldBe` expr
        it "sub2" $
            substitute expr "y" (v"x") `shouldNotBe` expr
        it "αEquiv" $
            (λ"x" # "y" --> v"x" $$ v"y") `shouldBe` (λ"y" # "x" --> v"y" $$ v"x")

-- test ideas
-- substitution of variable to variable should not be alpha equivalent unless same variable
-- Lemma 1.2.10: a equivalence has same free variables

\end{code}
