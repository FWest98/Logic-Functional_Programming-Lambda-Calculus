\begin{code}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Lambda (
    ΛCalculus(
        Variable, VariableName,
        fromVar, fromVarName, fromΛ, fromApp,
        prettyΛ, prettyLambda, showΛ, showLambda,
        freeVariables, αEquiv,
        renameVariable, prepareSubstitution, substitute, performSubstitute,
        βReductions, betaReductions,
        isNormalForm, normalForm, (===)
    )
) where

import Data.Set(Set, toList)

class ΛCalculus λ where
    type Variable λ
    type VariableName λ

    fromVar :: Variable λ -> λ
    fromVarName :: VariableName λ -> λ
    fromΛ :: Variable λ -> λ -> λ
    fromApp :: λ -> λ -> λ

    prettyΛ, prettyLambda :: λ -> String
    prettyLambda = prettyΛ
    showΛ, showLambda :: λ -> IO ()
    showLambda = showΛ

    freeVariables :: λ -> Set (VariableName λ)
    αEquiv :: λ -> λ -> [(Variable λ, Variable λ)] -> Bool

    renameVariable :: λ -> VariableName λ -> VariableName λ -> λ
    prepareSubstitution :: λ -> VariableName λ -> λ
    substitute, performSubstitute :: λ -> VariableName λ -> λ -> Maybe λ
    substitute λ var term = performSubstitute prepared var term
        where
            prepared = foldr (flip prepareSubstitution) λ $ toList $ freeVariables term

    βReductions, betaReductions :: λ -> [λ]
    betaReductions = βReductions

    isNormalForm :: λ -> Bool
    isNormalForm = null . βReductions

    βReduceLeft :: λ -> λ
    βReduceLeft term
     | isNormalForm term = error "The λ-term is already in normal form"
     | otherwise = head $ βReductions term

    normalForm :: λ -> λ
    normalForm term
     | isNormalForm term = term
     | otherwise = (normalForm . βReduceLeft) term

    (===) :: λ -> λ -> Bool
    x === y = x == y || normalForm x == normalForm y
    infix 1 ===

instance {-# OVERLAPPABLE #-} (ΛCalculus λ) => Eq λ where
    (==) :: λ -> λ -> Bool
    x == y = αEquiv x y []


\end{code}
