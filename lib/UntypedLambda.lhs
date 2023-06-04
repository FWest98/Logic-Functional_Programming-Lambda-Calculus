\section{Untyped Λ-calculus}

We will now discuss the implementation of a basic untyped $λ$-calculus. We will implement the standard type class we defined before, and we will focus on developer-friendliness in the syntax. From now on, we will skip module headers for brevity.

\ignore{
\begin{code}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}

-- Define module, list exports
module UntypedLambda (
    Λ, Lambda,
    λ, l, (-->), ($$)
) where

-- Imports
import Data.Set (Set, delete, union, singleton)
import Lambda
import Data.Maybe (isJust, fromJust)
\end{code}
\vspace{-23pt}
}

\begin{code}
-- Main defintions of lambda terms
data Λ = Var (Variable Λ) | Λ (Variable Λ) Λ | App Λ Λ
    deriving (Show)
type Lambda = Λ
\end{code}
\vspace{-23pt}

Here we define our main \hs!Λ! data type. It will be either a variable, an application, or a $λ$-abstraction. We do not derive \hs!Eq!, since that will be provided by the \hs!ΛCalculus! typeclass, to make \hs!Λ! an equivalence class under $α$-equivalence.

\begin{code}
instance Substitutable Λ String where
    -- Determining the set of free variables
    freeVariables :: Λ -> Set (Variable Λ)
    freeVariables (Var x)    = singleton x
    freeVariables (Λ x term) = delete x $ freeVariables term
    freeVariables (App x y)  = freeVariables x `union` freeVariables y

    -- Performing a substitution
    renameVariable :: Λ -> VariableName Λ -> VariableName Λ -> Λ
    renameVariable (Var x) old new
        | x == old  = Var new
        | otherwise = Var x
    renameVariable (Λ x term) old new
        | x == old  = Λ new $ renameVariable term old new
        | otherwise = Λ x   $ renameVariable term old new
    renameVariable (App x y) old new = App (renameVariable x old new) (renameVariable y old new)

    prepareSubstitution :: Λ -> VariableName Λ -> Λ
    prepareSubstitution (Λ x term) var
        | x /= var  = Λ x       $ prepareSubstitution term var
        | otherwise = Λ newName $ prepareSubstitution (renameVariable term x newName) var
        where newName = "_" ++ x
    prepareSubstitution (App x y) var = App (prepareSubstitution x var) (prepareSubstitution y var)
    prepareSubstitution var _ = var

    performSubstitution :: Λ -> Variable Λ -> Λ -> Maybe Λ
    performSubstitution (Var x) var term
        | x == var  = Just term
        | otherwise = Just $ Var x
    performSubstitution (Λ x t) var term
        | x == var  = Just $ Λ x t
        | otherwise = Λ x <$> performSubstitution t var term
    performSubstitution (App x y) var term = App <$> performSubstitution x var term <*> performSubstitution y var term
\end{code}
\vspace{-23pt}

The first action is to implement a notion of substitution on our data type. The definitions are relatively straightforward. One point of interest is the substitution preparation: it is not perfect as it will only prepend a single underscore to the variable name, which in more advanced cases might still yield conflicts. Furthermore, the actual substitution implementation uses \hs!Maybe!, since substitutions might fail in the generic case. For this implementation, that is not applicable.

\begin{code}
instance ΛCalculus Λ where
    type Variable Λ = String

    fromVar = Var
    fromVarName = Var
    fromΛ = Λ
    fromApp = App

    -- Pretty printing
    prettyΛ :: Λ -> String
    prettyΛ (Var x) = x
    prettyΛ (Λ x term@(Λ _ _))        = "λ" ++ x ++  tail (prettyΛ term)
    prettyΛ (Λ x term)                = "λ" ++ x ++ "." ++ prettyΛ term
    prettyΛ (App x@(Λ _ _) y@(Var _)) = "(" ++ prettyΛ x ++ ")"  ++ prettyΛ y
    prettyΛ (App x@(Λ _ _) y)         = "(" ++ prettyΛ x ++ ")(" ++ prettyΛ y ++ ")"
    prettyΛ (App x y@(Var _))         = prettyΛ x    ++     prettyΛ y
    prettyΛ (App x y)                 = prettyΛ x ++ "(" ++ prettyΛ y ++ ")"

    -- Defining the α-equivalence between pre-terms
    αEquiv :: Λ -> Λ -> [(Variable Λ, Variable Λ)] -> Bool
    αEquiv (Var x) (Var y) context          = x == y || (x, y) `elem` context
    αEquiv (Λ x xTerm) (Λ y yTerm) context  = notCrossBound && αEquiv xTerm yTerm ((x, y) : context)
        where
            yFreeInX = y `elem` freeVariables xTerm
            xFreeInY = x `elem` freeVariables yTerm
            notCrossBound = x == y || (not yFreeInX && not xFreeInY)
    αEquiv (App x1 x2) (App y1 y2) context  = αEquiv x1 y1 context && αEquiv x2 y2 context
    αEquiv _ _ _ = False

    -- Perform one of each possible β-redex in the lambda term
    βReductions :: Λ -> [Λ]
    βReductions (App (Λ x term) n) = [fromJust substitution | isJust substitution] ++ reduceTerm ++ reduceApp
        where
            reduceTerm = (\newTerm -> App (Λ x newTerm) n) <$> βReductions term
            reduceApp = App (Λ x term) <$> βReductions n
            substitution = substitute term x n
    βReductions (Var _)    = []
    βReductions (Λ x term) = Λ x <$> βReductions term
    βReductions (App x y)  = ((`App` y) <$> βReductions x) ++ (App x <$> βReductions y)
\end{code}
\vspace{-23pt}

The implementation of our typeclass is not particularly interesting. It has some pretty printing functionality that aims to resemble mathematical notation, and implements the default $α$-equivalence relation. The only interesting aspect there is how to deal with variable names that are bound in one expression and free in the other.

The more complicated part is the implementation of the $β$-reduction itself. This function will produce a list of all possible reductions. In most cases this is a simple recursive tree operation - the interesting case is where we have an application operating on an abstraction, which is a $β$-redex. There, we try to reduce the term itself through a substitution (which will always succeed in an untyped setting), but we also include reductions where we do not reduce this particular redex, but recurse further down into the data structure.

\subsection{Parsing}
From a coding perspective, the most interesting aspect of this implementation of an untyped $λ$-calculus is the `parsing' part we implement here. The objective is to develop a developer-friendly syntax for constructing $λ$-terms (instances of \hs!Λ!) without the need for a parser and with the benefit of compile-time syntax checking. The objective is to move from a syntax of \hs!Λ "x" (Λ "y" (App (Var "x") (Var "y")))! to the nicer \hs!λ"x" "y" --> "x" $$ "y"!. We do this by using variadic functions.
\begin{code}
-- Helper functions for notation
class ΛParameters a where
    toΛparameters :: [Variable Λ] -> a

instance ΛParameters (Λ -> Λ) where
    toΛparameters [] = error "No Λ-parameters supplied"
    toΛparameters [x] = Λ x
    toΛparameters (x:xs) = Λ x . toΛparameters xs

instance (ΛParameters a) => ΛParameters (String -> a) where
    toΛparameters xs x = toΛparameters (xs ++ [x])

λ,l :: ΛParameters a => a
l = λ
λ = toΛparameters []
\end{code}
\vspace{-23pt}

The idea behind the syntax introduced before is to let the arrow \hs!(-->)! separate the two `parts' of a $λ$-abstraction. The arrow will be an infix function that as its first argument accepts a `partial $λ$-term' - essentially a function that will accept a $λ$-term serving as body, returning another $λ$-term representing the entire abstraction.

This `partial $λ$-term' is implemented using a variadic function. Variadic functions in Haskell are implemented using recursive typeclasses - in this case \hs!ΛParameters!. We have two instances for this typeclass, one of our desired `return type' (\hs!Λ -> Λ!), and one of the `recursive case' (\hs!String -> a! for {\tt a} another instance of the typeclass). In addition, we have a `seed function' {\tt λ} that is just an arbitrary instance of the typeclass. So then, if we are writing \hs!λ"x" "y" --> ...!, GHC will deduce that everything to the left of the arrow will need to have type \hs!(Λ -> Λ)!, and thus {\tt λ} must be a function accepting two parameters and returning this function type. Since {\tt λ} itself just needs to be an instance of our typeclass, GHC will apply the `recursive' instance twice to obtain \hs!λ :: ΛParameters [String -> (ΛParameters [String -> (ΛParameters [Λ -> Λ])])]! (square brackets added to indicate how the typeclasses combine). Note that without the presence of {\tt (-->)} we would need to manually set the type of the partial term - Haskell won't know whether you want the `return type' or the `recursive case'. A defaulting mechanism would help alleviate this ambiguity, but the presence of {\tt (-->)} like will be the case in practice, this is not needed.

Now that we have the typeclasses with a recursive, variadic behaviour, we can focus on the implementation of them. This is essentially a `conversion' function from strings to functions \hs!Λ -> Λ!, where the `seed' will call it with an empty list, and the recursive typeclass instances will just append to this list and call the `next implementation' - all the way until the `return type' instance, that will convert the list of strings into a nested $λ$-abstraction that is just missing the `body'.

\begin{code}
class ΛTerm a where
    toΛ :: a -> Λ

instance ΛTerm Λ      where toΛ = id
instance ΛTerm String where toΛ = fromVarName

(-->) :: (ΛTerm a) => (Λ -> Λ) -> a -> Λ
a --> b = a (toΛ b)
infixr 6 -->

($$) :: (ΛTerm a, ΛTerm b) => a -> b -> Λ
x $$ y = App (toΛ x) (toΛ y)
infixl 7 $$
\end{code}
\vspace{-23pt}

This second part of parsing is a bit simpler: we now only need to construct some $λ$-term that is the body of our abstraction. To simplify notation, eliminating prefix calls to \hs!App!, we define an infix function \hs!($$)! that will do the same. To then further simplify notation, eliminating the need for \hs!Var!, we create a typeclass representing a generic $λ$-term that has instances of a string and an actual {\tt Λ} with a conversion function to always produce a {\tt Λ}.
