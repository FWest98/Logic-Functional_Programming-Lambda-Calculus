\section{Typed Λ-calculus}

Of all calculi implemented, this might be the least useful one: it is strongly constraint in expressivity due to the introduction of types, but since there is no quantification over types like in the polymorphic variant, it is not possible to write `generic' pair functions that work for every type - instead, for every type a new implementation has to be made.

However, from a coding perspective, this is a nice intermediate step between untyped and polymorphic versions: we can focus on introducing types, while keeping them still strictly separated from terms themselves.

\ignore{
\begin{code}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}

module TypedLambda (
    Λ, Lambda,
    λ, l, (-->), ($$), (==>), TypeableVariable((:::))
) where

-- Imports
import Lambda
import Helpers (lookupSet)
import Data.Maybe (isJust, fromJust, isNothing)
import Data.Set (Set, delete, union, singleton, insert, filter)
import Control.Monad
\end{code}
}

\begin{code}
data ΛVariable = (VariableName Λ) :-: (Type Λ)
    deriving (Show, Eq, Ord)
infixl 6 :-:

data Λ = Var ΛVariable | Λ ΛVariable Λ | App Λ Λ
    deriving (Show)
type Lambda = Λ
\end{code}
\vspace{-23pt}

This is mostly the same as for the untyped case, except that variables now deserve their own dedicated data type and are no longer simply strings. A variable here is now a string with an associated type - the \hs!Type! here is not a typeclass itself, but an instance of the type family inside the \hs!TypedΛCalculus! typeclass. Its definition will be given further down. We also set the correct fixity of the variable constructor.

\begin{code}
instance Substitutable Λ String where
    renameVariable :: Λ -> VariableName Λ -> VariableName Λ -> Λ
    renameVariable (Var (x :-: σ)) old new
        | x == old  = Var (new :-: σ)
        | otherwise = Var (x   :-: σ)
    renameVariable (Λ (x :-: σ) term) old new
        | x == old  = Λ (new :-: σ) $ renameVariable term old new
        | otherwise = Λ (x   :-: σ) $ renameVariable term old new
    renameVariable (App x y) old new = App (renameVariable x old new) (renameVariable y old new)

    prepareSubstitution :: Λ -> VariableName Λ -> Λ
    prepareSubstitution (Λ (x :-: σ) term) var
        | x /= var  = Λ (x       :-: σ) $ prepareSubstitution term var
        | otherwise = Λ (newName :-: σ) $ prepareSubstitution (renameVariable term x newName) var
        where newName = "_" ++ x
    prepareSubstitution (App x y) var = App (prepareSubstitution x var) (prepareSubstitution y var)
    prepareSubstitution var _ = var

    performSubstitution :: Λ -> VariableName Λ -> Λ -> Maybe Λ
    performSubstitution (Var (x :-: σ)) var term
        | x /= var              = Just $ Var (x :-: σ)
        | typeOf term /= Just σ = Nothing
        | otherwise             = Just term
    performSubstitution (Λ (x :-: σ) t) var term
        | x /= var              = Λ (x :-: σ) <$> performSubstitution t var term
        | otherwise             = Just $ Λ (x :-: σ) t
    performSubstitution (App x y) var term = App <$> performSubstitution x var term <*> performSubstitution y var term
\end{code}
\vspace{-23pt}

We have another implementation of \hs!Substitutable! to start off with, where most functions are an almost direct copy of the untyped case, but with some types sprinkled in. Only actually performing a substitution has become more complicated: we have to check the types of the variable to be substituted and the target $λ$-term. If they are not equivalent (in the simply-typed case: identical), then we cannot perform the substitution and we return \hs!Nothing!. Otherwise, the implementation is identical, and thus the {\tt freeVariables} implementation has been left out for brevity.

\ignore{
\begin{code}
    freeVariables :: Λ -> Set (VariableName Λ)
    freeVariables (Var (x :-: _))    = singleton x
    freeVariables (Λ (x :-: _) term) = delete x $ freeVariables term
    freeVariables (App x y)          = freeVariables x `union` freeVariables y
\end{code}
}

\begin{code}
instance ΛCalculus Λ where
    type Variable Λ = ΛVariable

    fromVar = Var
    fromVarName name = Var (name :-: Null)
    fromΛ = Λ
    fromApp = App

    prettyΛ :: Λ -> String
    prettyΛ (Var (x :-: Null))         = x
    prettyΛ (Var (x :-: σ))            = "(" ++ x ++ ":" ++ prettyType σ ++ ")"
    prettyΛ (Λ (x :-: σ) term@(Λ _ _)) = "λ" ++ x ++ ":" ++ prettyType σ ++ "," ++ tail (prettyΛ term)
    prettyΛ (Λ (x :-: σ) term)         = "λ" ++ x ++ ":" ++ prettyType σ ++ "." ++ prettyΛ term
    prettyΛ (App x@(Λ _ _) y@(Var _))  = "(" ++ prettyΛ x ++ ")"  ++ prettyΛ y
    prettyΛ (App x@(Λ _ _) y)          = "(" ++ prettyΛ x ++ ")(" ++ prettyΛ y ++ ")"
    prettyΛ (App x y@(Var _))          = prettyΛ x     ++    prettyΛ y
    prettyΛ (App x y)                  = prettyΛ x ++ "(" ++ prettyΛ y ++ ")"

    αEquiv :: Λ -> Λ -> EquivalenceContext Λ -> Bool
    αEquiv (Var (x :-: σ)) (Var (y :-: τ)) context
        = σ == τ && (x == y || (x, y) `elem` context)

    αEquiv (Λ (x :-: σ) xTerm) (Λ (y :-: τ) yTerm) context
        = notCrossBound && σ == τ && αEquiv xTerm yTerm ((x, y) : context)
        where
            yFreeInX = y `elem` freeVariables xTerm
            xFreeInY = x `elem` freeVariables yTerm
            notCrossBound = x == y || (not yFreeInX && not xFreeInY)

    αEquiv (App x1 x2) (App y1 y2) context = αEquiv x1 y1 context && αEquiv x2 y2 context
    αEquiv _ _ _ = False

    βReductions :: Λ -> [Λ]
    βReductions (App (Λ (x :-: σ) term) n) = [fromJust substitution | isJust substitution] ++ reduceTerm ++ reduceApp
        where
            reduceTerm  = (\newTerm -> App (Λ (x :-: σ) newTerm) n) <$> βReductions term
            reduceApp   = App (Λ (x :-: σ) term) <$> βReductions n
            substitution = substitute term x n
    βReductions (Var _)    = []
    βReductions (Λ x term) = Λ x <$> βReductions term
    βReductions (App x y)  = ((`App` y) <$> βReductions x) ++ (App x <$> βReductions y)
\end{code}
\vspace{-23pt}

The implementation of the \hs!ΛCalculus! typeclass itself also sees little change, with minor adaptations to the pretty printing. The $α$-equivalence now checks for type equality as well, and $β$-reduction is unchanged since type checking is handled in the substitution implementation.

\begin{code}
infixr 7 :->
instance TypedΛCalculus Λ where
    data Type Λ = Pure (VariableName Λ) | (Type Λ) :-> (Type Λ) | Perp | Null
        deriving (Show, Eq, Ord)
\end{code}
\vspace{-23pt}

Here we are getting to some more interesting aspects: the implementation of the type extensions in the \hs!TypedΛCalculus! typeclass. As mentioned before, we implement a type for our calculus using the type family defined on the typeclass. We have four cases: a pure type of some string (coinciding with variable names), a function type with infix constructor (and appropriate fixity), \hs!Perp! for inconsistent or impossible types, and \hs!Null! for unknown types (that we can fill using {\tt deduceTypes}).

\begin{code}
    prettyType :: Type Λ -> String
    prettyType (Pure σ)           = σ
    prettyType (σ@(Pure _) :-> τ) =        prettyType σ ++  "->" ++ prettyType τ
    prettyType (σ :-> τ)          = "(" ++ prettyType σ ++ ")->" ++ prettyType τ
    prettyType Null               = "?"
    prettyType Perp               = "⟂"

    typesEquivalent :: Type Λ -> Type Λ -> EquivalenceContext Λ -> Bool
    typesEquivalent x y _ = x == y
\end{code}
\vspace{-23pt}

Pretty printing is relatively straightforward, and type equivalence is just direct identity since we don't allow quantification over type variables - we defer that to the polymorphic case.

\begin{code}
    typeOf :: Λ -> Maybe (Type Λ)
    typeOf (Var (_ :-: σ))    = Just σ
    typeOf (Λ (_ :-: σ) term) = (σ :->) <$> typeOf term
    typeOf (App x y)          = join $ functionType <$> typeOf x <*> typeOf y
        where
            functionType :: Type Λ -> Type Λ -> Maybe (Type Λ)
            functionType (σ :-> τ) υ | σ == υ = Just τ
            functionType _ _ = Nothing
\end{code}
\vspace{-23pt}

The {\tt typeOf} function is somewhat interesting, as it has to deduce compound types from just the types of the variables. In our implementation of $λ$-terms, the terms themselves do not carry a type, only variables do. Especially the function application case is somewhat tricky, since we need to ensure that function and argument types align. If they do not, we return \hs!Nothing!.

\begin{code}
    deduceTypes :: Λ -> TypeMapping Λ -> Λ
    deduceTypes (Var (x :-: Null)) types
        | isJust mapping = Var (x :-: fromJust mapping)
        | otherwise      = Var (x :-: Null)
        where mapping = lookupSet x types
    deduceTypes (Var x) _ = Var x
    deduceTypes (Λ (x :-: σ) t) types = Λ (x :-: σ) $ deduceTypes t $ insert (x, σ) types
    deduceTypes (App xTerm (Var (x :-: Null))) types
        | not isFunction            = App deduceX (Var (x :-: Null))
        | isNothing mappedType      = App deduceX (Var (x :-: σ))
        | fromJust mappedType == σ  = App deduceX (Var (x :-: σ))
        | otherwise                 = App deduceX (Var (x :-: Null))
        where
            mappedType     = lookupSet x types
            functionType   = typeOf deduceX
            isFunction     = isJust functionType && case fromJust functionType of
                                                    (_ :-> _) -> True
                                                    _ -> False
            Just (σ :-> _) = functionType -- This will generate a warning but is explicitly safe here
            deduceX        = deduceTypes xTerm types

    deduceTypes (App x y) types = App (deduceTypes x types) (deduceTypes y types)
\end{code}
\vspace{-23pt}

The type deduction is probably the trickiest part of the entire implementation here. Our type deduction algorithm is focussed on `filling holes' in a $λ$-term, i.e. to replace \hs!Null! types with concrete ones. We use a \hs!TypeMapping! for this, a set of variables and their associated types. The cases for variables and $λ$-abstractions are relatively straightforward, but function application with just a variable of unknown type is the trickiest. We try to deduce the type in two ways: we try to determine the type of the function, and we see if the variable exists in our type mapping. When both are known, we check the two are the same, and otherwise we pick the appropriate one.

This function might not be able to fill all the holes, and then it will leave them empty. One could decide to instead replace these holes with \hs!Perp!, to indicate an inconsistent type. However, in our `parsing' implementation down below, we call this function continuously throughout term construction, and thus a judgement of \hs!Perp! might be premature. Leaving the holes empty allows us to repeatedly call this function to saturate the term more and more.

\begin{code}
    hasValidType :: Λ -> TypeMapping Λ -> Bool
    hasValidType (Var (x :-: σ)) vars    = (x, σ) `elem` vars
    hasValidType (Λ (x :-: σ) term) vars = hasValidType term (insert (x, σ) $ Data.Set.filter (\(y, _) -> x /= y) vars)
    hasValidType t@(App x y) vars        = hasValidType x vars && hasValidType y vars && isJust (typeOf t)
\end{code}
\vspace{-23pt}

Lastly, we have a simple type validity check. It will check whether the type is consistent: whether all variables are always used with the correct type and whether function application is valid as well.

\subsection{Parsing}
Once again, we implement a developer-friendly `parsing'. The setup is the same as for the untyped variant, except that variables are no longer only strings, but need to carry a type. The decision was made to always force a type for parameters in an abstraction, but to make types optional in the `body' of a term, where they can typically be deduced by the code above.

\begin{code}
class Typeable a where
    toType :: a -> Type Λ

instance Typeable (Type Λ) where toType = id
instance Typeable String where toType = Pure

(==>) :: (Typeable a, Typeable b) => a -> b -> Type Λ
a ==> b = toType a :-> toType b
infixr 7 ==>

data TypeableVariable where
    (:::) :: Typeable a => VariableName Λ -> a -> TypeableVariable
infixl 6 :::

toVariable :: TypeableVariable -> Variable Λ
toVariable (x ::: σ) = x :-: toType σ
\end{code}
\vspace{-23pt}

We first introduce a new typeclass, for parsing types more easily. Instead of having to write \hs!Pure "p" :-> Pure "q" :-> Pure "r"!, we introduce a typeclass \hs!Typeable! (in a similar fashion to \hs!ΛTerm! below) that allows us to convert both types and strings to a type. Since our \hs!ΛVariable! definition only accepts a \hs!Type Λ! instance, and not a generic \hs!Typeable! instance, we introduce a custom data type \hs!TypeableVariable! that allows us to combine a variable name with a generic type, providing a function to convert it all into a proper instance of \hs!Type Λ!. The rest of the parsing code is nearly identical to the untyped version, to we omit it for brevity. The main change in there is that upon every application of {\tt \$\$}, we call {\tt deduceTypes} to fill the type holes as we go.

\ignore{
\begin{code}
class ΛParameters a where
    toΛparameters :: [Variable Λ] -> a

instance ΛParameters (Λ -> Λ) where
    toΛparameters [] = error "No Λ-parameters supplied"
    toΛparameters [x] = Λ x
    toΛparameters (x:xs) = Λ x . toΛparameters xs

instance (ΛParameters a) => ΛParameters (ΛVariable -> a) where
    toΛparameters xs x = toΛparameters (xs ++ [x])

instance (ΛParameters a) => ΛParameters (TypeableVariable -> a) where
    toΛparameters xs x = toΛparameters (xs ++ [toVariable x])

λ, l :: ΛParameters a => a
l = λ
λ = toΛparameters []

class ΛTerm a where
    toΛ :: a -> Λ

instance ΛTerm Λ                where toΛ = id
instance ΛTerm String           where toΛ = fromVarName
instance ΛTerm TypeableVariable where toΛ = Var . toVariable

(-->) :: ΛTerm a => (Λ -> Λ) -> a -> Λ
a --> b = deduceTypes (a (toΛ b)) mempty
infixr 5 -->

($$) :: (ΛTerm a, ΛTerm b) => a -> b -> Λ
x $$ y = App (toΛ x) (toΛ y)
infixl 6 $$
\end{code}
\vspace{-23pt}
}

Even though the parsing code is so similar to the untyped case, with many shared typeclasses and implementations, unfortunately the implementation could not be made more generic for any instance of \hs!ΛCalculus! due to limitations in the Haskell typing system. Essentially, in an expression like \hs!λ("x" ::: "σ") --> "x" $$ "y"!, the type of neither {\tt (-->)} nor \hs!($$)! can be deduced: the arrow knows that it should return a {\tt Λ}, but does not know what the term-type of its RHS will be (string or {\tt Λ}), while the {\tt \$\$} function does not know what the `target calculus' is - it only knows what type of variables it deals with. Even though it seems like this should be solvable, it turns out to be impossible in Haskell.
