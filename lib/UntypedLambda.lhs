\begin{code}

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
module Lambda (
    Λ, Lambda,
    λ, l, (-->), ($$),
    prettyΛ, prettyLambda, showΛ, showLambda,
    freeVariables, substitute,
    isNormalForm, βReductions, betaReductions, normalForm, (===)
) where

-- Imports
import Data.Set (Set, delete, union, singleton)

-- Main defintions of lambda terms
type Variable = String
data Λ = Var Variable | Λ Variable Λ | App Λ Λ
    deriving (Show)
type Lambda = Λ

-- Defining the α-equivalence between pre-terms
type EquivalenceContext = [(Variable, Variable)]

αEquiv :: Λ -> Λ -> EquivalenceContext -> Bool
αEquiv (Var x) (Var y) context = x == y || (x, y) `elem` context
αEquiv (Λ x xTerm) (Λ y yTerm) context = canSubstitute && αEquiv xTerm yTerm ((x, y) : context)
  where
    yInXTerm = y `elem` freeVariables xTerm
    xInYTerm = x `elem` freeVariables yTerm
    canSubstitute = not yInXTerm && not xInYTerm

αEquiv (App x1 x2) (App y1 y2) context = αEquiv x1 y1 context && αEquiv x2 y2 context
αEquiv _ _ _ = False

instance Eq Λ where
  x == y = αEquiv x y []

-- Helper functions for notation
class ΛParams a where
  toΛparams :: [Variable] -> a

instance ΛParams (Λ -> Λ) where
  toΛparams [] = error "No Λ parameters supplied"
  toΛparams [x] = Λ x
  toΛparams (x:xs) = Λ x . toΛparams xs

instance (ΛParams a) => ΛParams (Variable -> a) where
  toΛparams xs x = toΛparams (xs ++ [x])

λ,l :: ΛParams a => a
λ = toΛparams []
l = λ

class Λable a where
  toΛ :: a -> Λ

instance Λable Λ where toΛ = id
instance Λable String where toΛ = Var

(-->) :: Λable a => (Λ -> Λ) -> a -> Λ
a --> b = a (toΛ b)
infixr 6 -->

($$) :: (Λable a, Λable b) => a -> b -> Λ
x $$ y = App (toΛ x) (toΛ y)
infixl 7 $$

-- Pretty printing
prettyΛ, prettyLambda :: Λ -> String
prettyLambda = prettyΛ
prettyΛ (Var x) = x
prettyΛ (Λ x term@(Λ _ _)) = "λ" ++ x ++ tail (prettyΛ term)
prettyΛ (Λ x term) = "λ" ++ x ++ "." ++ prettyΛ term
prettyΛ (App x@(Λ _ _) y@(Var _)) = "(" ++ prettyΛ x ++ ")" ++ prettyΛ y
prettyΛ (App x@(Λ _ _) y) = "(" ++ prettyΛ x ++ ")(" ++ prettyΛ y ++ ")"
prettyΛ (App x y@(Var _)) = prettyΛ x ++ prettyΛ y
prettyΛ (App x y) = prettyΛ x ++ "(" ++ prettyΛ y ++ ")"

showΛ, showLambda :: Λ -> IO ()
showLambda = showΛ
showΛ = putStrLn . prettyΛ

-- Determining the set of free variables
freeVariables :: Λ -> Set Variable
freeVariables (Var x) = singleton x
freeVariables (Λ x term) = delete x $ freeVariables term
freeVariables (App x y) = freeVariables x `union` freeVariables y

-- Performing a substitution
substitute :: Λ -> Variable -> Λ -> Λ
substitute (Var x) var term
                            | x == var = term
                            | otherwise = Var x
substitute (Λ x t) var term
                            | x == var = Λ x t
                            | otherwise = Λ x (substitute t var term)
substitute (App x y) var term = App (substitute x var term) (substitute y var term)

-- Finding whether there are any β-redexes
hasβRedex :: Λ -> Bool
hasβRedex (App (Λ _ _) _) = True
hasβRedex (Var _) = False
hasβRedex (Λ _ term) = hasβRedex term
hasβRedex (App x y) = hasβRedex x || hasβRedex y

isNormalForm :: Λ -> Bool
isNormalForm = not . hasβRedex

-- Perform one of each possible β-redex in the lambda term
βReductions, betaReductions :: Λ -> [Λ]
betaReductions = βReductions
βReductions (App (Λ x term) n) = [substitute term x n] ++ reduceTerm ++ reduceApp
    where
        reduceTerm = (\newTerm -> App (Λ x newTerm) n) <$> βReductions term
        reduceApp = App (Λ x term) <$> βReductions n
βReductions (Var _) = []
βReductions (Λ x term) = Λ x <$> βReductions term
βReductions (App x y) = ((`App` y) <$> βReductions x) ++ (App x <$> βReductions y)

-- Performing only the leftmost redex to try and find the normal form - if it exists
βReduceLeft :: Λ -> Λ
βReduceLeft t
 | hasβRedex t = head $ βReductions t
 | otherwise = error "The λ-term is already in normal form!"

normalForm :: Λ -> Λ
normalForm t
 | isNormalForm t = t
 | otherwise = (normalForm . βReduceLeft) t

-- Rudimentary β-equivalence relation.
-- It is complete for terms with a normal form - but without a normal form we will
-- need a more sophisticated algorithm that would do some kind of search through all
-- possible reduction paths.
(===) :: Λ -> Λ -> Bool
x === y = x == y || normalForm x == normalForm y
infix 1 ===

\end{code}
