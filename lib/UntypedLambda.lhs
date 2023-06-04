\begin{code}

{-# LANGUAGE TypeFamilies #-}

{-

Basic machinery for an untyped lambda calculus. The main data type Λ represents
a lambda term (i.e. an equivalence class of pre-terms under the αEquiv relation).

We include definitions for determining the set of free variables in a lambda term,
as well as performing substitutions and β-reductions. A normal form finder that will
only reduce the leftmost redex is implemented as well. In addition, a rudimentary,
non-complete β-equivalence relation (===) is provided - it works properly only on
weakly normalising terms.

Lastly, some helper functions are provided to make notation of lambda terms in code
easier. These provide an infix notation using the common shorthand rules, for example:
the mathematical notation λxy.xy corresponds to {λ "x" # "y" --> v"x" $$ v"y"}. This is
more readable than {Λ "x" (Λ "y" (App (Var "x") (Var "y")))}.

-}

-- Define module, list exports
module UntypedLambda (
    Λ, Lambda,
    λ, l, (-->), ($$)
) where

-- Imports
import Data.Set (Set, delete, union, singleton)
import Lambda
import Data.Maybe (isJust, fromJust)

-- Main defintions of lambda terms
type ΛVariable = String
data Λ = Var ΛVariable | Λ ΛVariable Λ | App Λ Λ
    deriving (Show)
type Lambda = Λ

instance ΛCalculus Λ where
    type VariableName Λ = ΛVariable
    type Variable Λ = ΛVariable

    fromVar = Var
    fromVarName = Var
    fromΛ = Λ
    fromApp = App

    -- Pretty printing
    prettyΛ :: Λ -> String
    prettyΛ (Var x) = x
    prettyΛ (Λ x term@(Λ _ _)) = "λ" ++ x ++ tail (prettyΛ term)
    prettyΛ (Λ x term) = "λ" ++ x ++ "." ++ prettyΛ term
    prettyΛ (App x@(Λ _ _) y@(Var _)) = "(" ++ prettyΛ x ++ ")" ++ prettyΛ y
    prettyΛ (App x@(Λ _ _) y) = "(" ++ prettyΛ x ++ ")(" ++ prettyΛ y ++ ")"
    prettyΛ (App x y@(Var _)) = prettyΛ x ++ prettyΛ y
    prettyΛ (App x y) = prettyΛ x ++ "(" ++ prettyΛ y ++ ")"

    showΛ :: Λ -> IO ()
    showΛ = putStrLn . prettyΛ

    -- Determining the set of free variables
    freeVariables :: Λ -> Set ΛVariable
    freeVariables (Var x) = singleton x
    freeVariables (Λ x term) = delete x $ freeVariables term
    freeVariables (App x y) = freeVariables x `union` freeVariables y

    -- Defining the α-equivalence between pre-terms
    αEquiv :: Λ -> Λ -> [(ΛVariable, ΛVariable)] -> Bool
    αEquiv (Var x) (Var y) context = x == y || (x, y) `elem` context
    αEquiv (Λ x xTerm) (Λ y yTerm) context = notCrossBound && αEquiv xTerm yTerm ((x, y) : context)
        where
            yFreeInX = y `elem` freeVariables xTerm
            xFreeInY = x `elem` freeVariables yTerm
            notCrossBound = x == y || not yFreeInX && not xFreeInY

    αEquiv (App x1 x2) (App y1 y2) context = αEquiv x1 y1 context && αEquiv x2 y2 context
    αEquiv _ _ _ = False

    -- Performing a substitution
    renameVariable :: Λ -> VariableName Λ -> VariableName Λ -> Λ
    renameVariable (Var x) old new
        | x == old = Var new
        | otherwise = Var x
    renameVariable (Λ x term) old new
        | x == old = Λ new $ renameVariable term old new
        | otherwise = Λ x $ renameVariable term old new
    renameVariable (App x y) old new = App (renameVariable x old new) (renameVariable y old new)

    prepareSubstitution :: Λ -> VariableName Λ -> Λ
    prepareSubstitution (Λ x term) var
        | x /= var  = Λ x $ prepareSubstitution term var
        | otherwise = Λ newName $ prepareSubstitution (renameVariable term x newName) var
        where newName = "_" ++ x
    prepareSubstitution (App x y) var = App (prepareSubstitution x var) (prepareSubstitution y var)
    prepareSubstitution var _ = var

    performSubstitute :: Λ -> Variable Λ -> Λ -> Maybe Λ
    performSubstitute (Var x) var term
        | x == var = Just term
        | otherwise = Just $ Var x
    performSubstitute (Λ x t) var term
        | x == var = Just $ Λ x t
        | otherwise = Λ x <$> performSubstitute t var term
    performSubstitute (App x y) var term = App <$> performSubstitute x var term <*> performSubstitute y var term

    -- Perform one of each possible β-redex in the lambda term
    βReductions :: Λ -> [Λ]
    βReductions (App (Λ x term) n) = [fromJust substitution | isJust substitution] ++ reduceTerm ++ reduceApp
        where
            reduceTerm = (\newTerm -> App (Λ x newTerm) n) <$> βReductions term
            reduceApp = App (Λ x term) <$> βReductions n
            substitution = substitute term x n
    βReductions (Var _) = []
    βReductions (Λ x term) = Λ x <$> βReductions term
    βReductions (App x y) = ((`App` y) <$> βReductions x) ++ (App x <$> βReductions y)

-- Helper functions for notation
class ΛParameters a where
    toΛparameters :: [ΛVariable] -> a

instance ΛParameters (Λ -> Λ) where
    toΛparameters [] = error "No Λ-parameters supplied"
    toΛparameters xs = \λbody -> foldr fromΛ λbody xs

instance (ΛParameters a) => ΛParameters (ΛVariable -> a) where
    toΛparameters xs x = toΛparameters (xs ++ [x])

λ,l :: ΛParameters a => a
l = λ
λ = toΛparameters []

class ΛTerm a where
    toΛ :: a -> Λ

instance ΛTerm Λ where toΛ = id
instance ΛTerm ΛVariable where toΛ = fromVarName

(-->) :: (ΛTerm a) => (Λ -> Λ) -> a -> Λ
a --> b = a (toΛ b)
infixr 6 -->

($$) :: (ΛTerm a, ΛTerm b) => a -> b -> Λ
x $$ y = fromApp (toΛ x) (toΛ y)
infixl 7 $$

\end{code}
