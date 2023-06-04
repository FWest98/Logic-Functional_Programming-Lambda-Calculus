\begin{code}

{-# LANGUAGE TypeFamilies #-}

module TypedLambda (
    Λ, Lambda, Type,
    λ, l, (-->), ($$), (==>), TypeableVariable((:::))
) where
-- Imports
import Lambda
import Helpers (lookupSet)
import Data.Maybe (isJust, fromJust, isNothing)
import Data.Set (Set, delete, union, singleton, insert, filter)
import Control.Monad

data ΛVariable = (VariableName Λ) :-: (Type Λ)
    deriving (Show, Eq, Ord)
data Λ = Var ΛVariable | Λ ΛVariable Λ | App Λ Λ
    deriving (Show)
type Lambda = Λ

infixr 7 :->
infixl 6 :-:

instance ΛCalculus Λ where
    type Variable Λ = ΛVariable

    fromVar = Var
    fromVarName name = Var (name :-: Null)
    fromΛ = Λ
    fromApp = App

    prettyΛ :: Λ -> String
    prettyΛ (Var (x :-: Null)) = x
    prettyΛ (Var (x :-: σ)) = "(" ++ x ++ ":" ++ prettyType σ ++ ")"
    prettyΛ (Λ (x :-: σ) term@(Λ _ _)) = "λ" ++ x ++ ":" ++ prettyType σ ++ "," ++ tail (prettyΛ term)
    prettyΛ (Λ (x :-: σ) term) = "λ" ++ x ++ ":" ++ prettyType σ ++ "." ++ prettyΛ term
    prettyΛ (App x@(Λ _ _) y@(Var _)) = "(" ++ prettyΛ x ++ ")" ++ prettyΛ y
    prettyΛ (App x@(Λ _ _) y) = "(" ++ prettyΛ x ++ ")(" ++ prettyΛ y ++ ")"
    prettyΛ (App x y@(Var _)) = prettyΛ x ++ prettyΛ y
    prettyΛ (App x y) = prettyΛ x ++ "(" ++ prettyΛ y ++ ")"

    freeVariables :: Λ -> Set (VariableName Λ)
    freeVariables (Var (x :-: _)) = singleton x
    freeVariables (Λ (x :-: _) term) = delete x $ freeVariables term
    freeVariables (App x y) = freeVariables x `union` freeVariables y

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

    renameVariable :: Λ -> VariableName Λ -> VariableName Λ -> Λ
    renameVariable (Var (x :-: σ)) old new
        | x == old = Var (new :-: σ)
        | otherwise = Var (x :-: σ)
    renameVariable (Λ (x :-: σ) term) old new
        | x == old = Λ (new :-: σ) $ renameVariable term old new
        | otherwise = Λ (x :-: σ) $ renameVariable term old new
    renameVariable (App x y) old new = App (renameVariable x old new) (renameVariable y old new)

    prepareSubstitution :: Λ -> VariableName Λ -> Λ
    prepareSubstitution (Λ (x :-: σ) term) var
        | x /= var  = Λ (x :-: σ) $ prepareSubstitution term var
        | otherwise = Λ (newName :-: σ) $ prepareSubstitution (renameVariable term x newName) var
        where newName = "_" ++ x
    prepareSubstitution (App x y) var = App (prepareSubstitution x var) (prepareSubstitution y var)
    prepareSubstitution var _ = var

    performSubstitute :: Λ -> VariableName Λ -> Λ -> Maybe Λ
    performSubstitute (Var (x :-: σ)) var term
        | x /= var = Just $ Var (x :-: σ)
        | typeOf term /= Just σ = Nothing
        | otherwise = Just term
    performSubstitute (Λ (x :-: σ) t) var term
        | x /= var = Λ (x :-: σ) <$> performSubstitute t var term
        | otherwise = Just $ Λ (x :-: σ) t
    performSubstitute (App x y) var term = App <$> performSubstitute x var term <*> performSubstitute y var term

    βReductions :: Λ -> [Λ]
    βReductions (App (Λ (x :-: σ) term) n) = [fromJust substitution | isJust substitution] ++ reduceTerm ++ reduceApp
        where
            reduceTerm = (\newTerm -> App (Λ (x :-: σ) newTerm) n) <$> βReductions term
            reduceApp = App (Λ (x :-: σ) term) <$> βReductions n
            substitution = substitute term x n
    βReductions (Var _) = []
    βReductions (Λ x term) = Λ x <$> βReductions term
    βReductions (App x y) = ((`App` y) <$> βReductions x) ++ (App x <$> βReductions y)

instance TypedΛCalculus Λ where
    data Type Λ = Pure (VariableName Λ) | (Type Λ) :-> (Type Λ) | Perp | Null
        deriving (Show, Eq, Ord)

    prettyType :: Type Λ -> String
    prettyType (Pure σ) = σ
    prettyType (σ@(Pure _) :-> τ) = prettyType σ ++ "->" ++ prettyType τ
    prettyType (σ :-> τ) = "(" ++ prettyType σ ++ ")->" ++ prettyType τ
    prettyType Null = "?"
    prettyType Perp = "⟂"

    typesEquivalent :: Type Λ -> Type Λ -> EquivalenceContext Λ -> Bool
    typesEquivalent x y _ = x == y

    typeOf :: Λ -> Maybe (Type Λ)
    typeOf (Var (_ :-: σ)) = Just σ
    typeOf (Λ (_ :-: σ) term) = (σ :->) <$> typeOf term
    typeOf (App x y)
        = join $ functionType <$> typeOf x <*> typeOf y
        where
            functionType :: Type Λ -> Type Λ -> Maybe (Type Λ)
            functionType (σ :-> τ) υ
                | σ == υ = Just τ
                | otherwise = Nothing
            functionType _ _ = Nothing

    renameType :: Type Λ -> VariableName Λ -> VariableName Λ -> Type Λ
    renameType (Pure σ) old new
     | σ /= old  = Pure σ
     | otherwise = Pure new
    renameType (σ :-> τ) old new = renameType σ old new :-> renameType τ old new
    renameType σ _ _ = σ

    deduceTypes :: Λ -> TypeMapping Λ -> Λ
    deduceTypes (Var (x :-: Null)) types
        | isJust mapping = Var (x :-: fromJust mapping)
        | otherwise = Var (x :-: Null)
        where mapping = lookupSet x types
    deduceTypes (Var x) _ = Var x
    deduceTypes (Λ (x :-: σ) t) types = Λ (x :-: σ) $ deduceTypes t $ insert (x, σ) types
    deduceTypes (App xTerm (Var (x :-: Null))) types
        | not isFunction = App deduceX (Var (x :-: Null))
        | isNothing mappedType = App deduceX (Var (x :-: σ))
        | fromJust mappedType == σ = App deduceX (Var (x :-: σ))
        | otherwise = App deduceX (Var (x :-: Null))
        where
            mappedType = lookupSet x types
            functionType = typeOf deduceX
            isFunction = isJust functionType && case fromJust functionType of
                                                    (_ :-> _) -> True
                                                    _ -> False
            Just (σ :-> _) = functionType
            deduceX = deduceTypes xTerm types

    deduceTypes (App x y) types = App (deduceTypes x types) (deduceTypes y types)

    hasValidType :: Λ -> TypeMapping Λ -> Bool
    hasValidType (Var (x :-: σ)) vars = (x, σ) `elem` vars
    hasValidType (Λ (x :-: σ) term) vars = hasValidType term (insert (x, σ) $ Data.Set.filter (\(y, _) -> x /= y) vars)
    hasValidType t@(App x y) vars = hasValidType x vars && hasValidType y vars && isJust (typeOf t)

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

class Typeable a where
  toType :: a -> Type Λ

instance Typeable (Type Λ) where toType = id
instance Typeable String where toType = Pure

(==>) :: (Typeable a, Typeable b) => a -> b -> Type Λ
a ==> b = toType a :-> toType b
infixr 7 ==>

class ΛTerm a where
  toΛ :: a -> Λ

instance ΛTerm Λ where toΛ = id
instance ΛTerm String where toΛ s = Var (s :-: Null)
instance ΛTerm TypeableVariable where toΛ = Var . toVariable

(-->) :: ΛTerm a => (Λ -> Λ) -> a -> Λ
a --> b = deduceTypes (a (toΛ b)) mempty
infixr 5 -->

($$) :: (ΛTerm a, ΛTerm b) => a -> b -> Λ
x $$ y = App (toΛ x) (toΛ y)
infixl 6 $$

data TypeableVariable where
  (:::) :: Typeable a => VariableName Λ -> a -> TypeableVariable
infixl 6 :::

toVariable :: TypeableVariable -> Variable Λ
toVariable (x ::: σ) = x :-: toType σ

\end{code}
