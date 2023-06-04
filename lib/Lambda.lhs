\section{Typeclasses}

We start our work by defining some useful typeclasses to represent generic substitutable terms, generic $λ$-calculi, and a typability extension to the generic \hs!ΛCalculus!-typeclass.

\begin{code}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

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
\end{code}
\vspace{-23pt}

This is a simple module header with some language features and imports - nothing special yet.

\begin{code}
class Substitutable term var | term -> var where
    freeVariables :: term -> Set var
    renameVariable :: term -> var -> var -> term
    prepareSubstitution :: term -> var -> term
    performSubstitution :: term -> var -> term -> Maybe term
    substitute :: term -> var -> term -> Maybe term
    substitute term var new = performSubstitution prepared var new
        where prepared = foldr (flip prepareSubstitution) term $ toList $ freeVariables new
\end{code}
\vspace{-23pt}

Here we define a basic \hs!Substitutable! typeclass. It is intended to represent any terms with variables on which a substitution can be performed. This will later be re-used for both $λ$-terms as well as type expressions in the polymorphic calculus. The name of the function \hs!freeVariables! is slightly influenced by the intended usage context, it is supposed to be the list of `eligible substitution targets'.

The implementation of the substitution itself is split in three parts: analysis, preparation, and substitution itself. The intention is to prevent accidental name clashes after substitution, leading to potentially unwanted variable binding. For example, when $β$-reducing $(λxy.x)y \to_β (λy.x)[x := y]$ we want to prevent simply replacing $x$ by $y$, since then suddenly the binding of $y$ changes from a free variable to bound by our $λ$. Instead, we want to rename our bound variable before substituting: $(λy.x)[x := y] = (λy'.x)[x := y] \to_β λy'.y$. This is exactly what is done in \hs!prepareSubstitution! for every potentially conflicting (`free') variable in the substitution target.

\begin{code}
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
\end{code}
\vspace{-23pt}

Here we have defined the type class for a generic $λ$-calculus. We define two type families, \hs!Variable λ! and \hs!VariableName λ! that will have an instance for each instance of the type class. For the variable name, we provide a default instance with \hs!String!. We define some default constructors that will be relevant for all calculi, and define and implement some pretty printing logic. The pretty printing is not intended to generate valid Haskell code, but should instead print something more human-readable. We also implement some show functions that will print directly to \hs!IO!, as otherwise the unicode characters in the text will be encoded by \hs!Show!.

Afterwards, we define the `meat' of the any calculus: a notion of $α$-equivalence and $β$-reduction. We define a termination criterion for finding the $β$-normal form, as well as a rudimentary normal form finding that will simply only contract the leftmost redex until it reaches termination. For non-strongly normalising calculi, this function might not terminate. Lastly, we define \hs!(===)! to be $β$-equivalence.

\begin{code}
instance {-# OVERLAPPABLE #-} (ΛCalculus λ) => Eq λ where
    (==) :: λ -> λ -> Bool
    x == y = αEquiv x y []
\end{code}
\vspace{-23pt}

For each instance of our \hs!ΛCalculus! type class, we provide an instance of \hs!Eq! that will identify two $λ$-terms when they are $α$-equivalent. This provides us with a versatile notion of equality that is intuitive to most users. Together with the previously-defined \hs!(===)! operation, we cover most bases. Note that this instance is labelled \hs!{-# OVERLAPPABLE #-}!. This indicates to GHC that even though this instance might overlap with other \hs!Eq! instances, the other instance should be picked with priority. This prevents issues with the open-world assumption in GHC, where an instance \hs!ΛCalculus Int! {\it might} exist, conflicting with the `traditional' instance for \hs!Int!.

\begin{code}
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
\vspace{-23pt}

At the end of our typeclass adventure we define some extensions to \hs!ΛCalculus! tailored to typed calculi. We define another type family, this time a family of \hs!data! definitions. In contrast to \hs!type! families, \hs!data! families allow us to uniquely identify a single \hs!Type λ! to each implementation of \hs!TypedΛCalculus λ!. As a consequence, we know that if \hs!Type λ1 == Type λ2!, then \hs!λ1 == λ2!, which in turn enables us to define class instances for the \hs!Type λ! - which is what we do for \hs!Eq! again to provide a type equivalence.
