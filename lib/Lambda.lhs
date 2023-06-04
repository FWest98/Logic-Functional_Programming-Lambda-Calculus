\begin{code}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module Lambda (
    Substitutable (
        freeVariables, renameVariable,
        prepareSubstitution, substitute, performSubstitution
    ),
    ΛCalculus (
        Variable, VariableName,
        fromVar, fromVarName, fromΛ, fromApp,
        prettyΛ, prettyLambda, showΛ, showLambda,
        αEquiv, βReductions, betaReductions,
        isNormalForm, normalForm, (===)
    ),
    EquivalenceContext,
    TypedΛCalculus (
        Type,
        prettyType, showType, showTermType,
        typeOf, typesEquivalent,
        deduceTypes, hasValidType
    ),
    TypeMapping
) where

import Data.Set(Set, toList)

class Substitutable term var | term -> var where
    freeVariables :: term -> Set var
    renameVariable :: term -> var -> var -> term
    prepareSubstitution :: term -> var -> term
    performSubstitution :: term -> var -> term -> Maybe term
    substitute :: term -> var -> term -> Maybe term
    substitute term var new = performSubstitution prepared var new
        where prepared = foldr (flip prepareSubstitution) term $ toList $ freeVariables new

class ΛCalculus λ where
    type Variable λ
    type VariableName λ
    type VariableName λ = String

    -- Some kind of constructors
    fromVar     :: Variable λ -> λ
    fromVarName :: VariableName λ -> λ
    fromΛ       :: Variable λ -> λ -> λ
    fromApp     :: λ -> λ -> λ

    -- Pretty printing intended just for the end user, including some
    -- equivalent show functions that will print to IO, taking care of
    -- unicode properly (Show on a unicode string will not print the
    -- unicode characters properly)
    prettyΛ, prettyLambda :: λ -> String
    prettyLambda = prettyΛ
    showΛ, showLambda :: λ -> IO ()
    showLambda = showΛ
    showΛ = putStrLn . prettyΛ

    αEquiv :: λ -> λ -> EquivalenceContext λ -> Bool

    βReductions, betaReductions :: λ -> [λ]
    betaReductions = βReductions

    isNormalForm :: λ -> Bool
    isNormalForm = null . βReductions

    -- If there is a normal form, then it can be achieved with repeated
    -- contraction of the leftmost redex.
    βReduceLeft :: λ -> λ
    βReduceLeft term
     | isNormalForm term = error "The λ-term is already in normal form"
     | otherwise         = head $ βReductions term

    normalForm :: λ -> λ
    normalForm term
     | isNormalForm term = term
     | otherwise         = (normalForm . βReduceLeft) term

    -- β-equivalence relation that we will identify with ===
    (===) :: λ -> λ -> Bool
    x === y = x == y || normalForm x == normalForm y
    infix 1 ===

type EquivalenceContext λ = [(VariableName λ, VariableName λ)]

instance {-# OVERLAPPABLE #-} (ΛCalculus λ) => Eq λ where
    (==) :: λ -> λ -> Bool
    x == y = αEquiv x y []

class (ΛCalculus λ) => TypedΛCalculus λ where
    data Type λ

    prettyType :: Type λ -> String
    
    showType :: Type λ -> IO ()
    showType = putStrLn . prettyType

    showTermType :: λ -> IO ()
    showTermType term = putStrLn $ maybe "Impossible type" prettyType (typeOf term)

    typesEquivalent :: Type λ -> Type λ -> EquivalenceContext λ -> Bool
    typeOf :: λ -> Maybe (Type λ)

    deduceTypes  :: λ -> TypeMapping λ -> λ
    hasValidType :: λ -> TypeMapping λ -> Bool

type TypeMapping λ = Set (VariableName λ, Type λ)

instance {-# OVERLAPPABLE #-} (TypedΛCalculus λ) => Eq (Type λ) where
    (==) :: Type λ -> Type λ -> Bool
    σ == τ = typesEquivalent σ τ []

\end{code}
