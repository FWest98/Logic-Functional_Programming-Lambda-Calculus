\begin{code}

-- aka System F

{-# LANGUAGE TypeFamilies #-}

module PolymorphicLambda (
    Λ, Lambda,
    λ, l, λT, lT, (-->), ($$),
    (==>), TypeableVariable((:::)),
    Type (Forall)
) where

-- Imports
import Lambda
import Helpers
import Data.Set (Set, delete, singleton, union, empty, insert, filter)
import Control.Monad
import Data.Maybe

data ΛVariable = (VariableName Λ) :-: (Type Λ)
  deriving (Show, Eq, Ord)
data Λ = Var ΛVariable | Λ ΛVariable Λ | ΛT (VariableName Λ) Λ | App Λ Λ
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
    prettyΛ (Var (x :-: Type)) = x
    prettyΛ (Var (x :-: σ)) = "(" ++ x ++ ":" ++ prettyType σ ++ ")"
    prettyΛ (Λ (x :-: σ) term@(Λ _ _)) = "λ" ++ x ++ ":" ++ prettyType σ ++ "," ++ tail (prettyΛ term)
    prettyΛ (Λ (x :-: σ) term) = "λ" ++ x ++ ":" ++ prettyType σ ++ "." ++ prettyΛ term
    prettyΛ (ΛT x term@(ΛT _ _)) = "Λ" ++ x ++ "," ++ tail (prettyΛ term)
    prettyΛ (ΛT x term) = "Λ" ++ x ++ prettyΛ term
    prettyΛ (App x@(Λ _ _) y@(Var _)) = "(" ++ prettyΛ x ++ ")" ++ prettyΛ y
    prettyΛ (App x@(Λ _ _) y) = "(" ++ prettyΛ x ++ ")(" ++ prettyΛ y ++ ")"
    prettyΛ (App x@(ΛT _ _) y@(Var _)) = "(" ++ prettyΛ x ++ ")" ++ prettyΛ y
    prettyΛ (App x@(ΛT _ _) y) = "(" ++ prettyΛ x ++ ")(" ++ prettyΛ y ++ ")"
    prettyΛ (App x y@(Var _)) = prettyΛ x ++ prettyΛ y
    prettyΛ (App x y) = prettyΛ x ++ "(" ++ prettyΛ y ++ ")"

    freeVariables :: Λ -> Set (VariableName Λ)
    freeVariables (Var (x :-: σ)) = insert x $ freeTypeVariables σ
    freeVariables (Λ (x :-: _) term) = delete x $ freeVariables term
    freeVariables (ΛT p term) = delete p $ freeVariables term
    freeVariables (App x y) = freeVariables x `union` freeVariables y

    αEquiv :: Λ -> Λ -> EquivalenceContext Λ -> Bool
    αEquiv (Var (x :-: σ)) (Var (y :-: τ)) context
        = typesEquivalent σ τ context && (x == y || (x, y) `elem` context)

    αEquiv (Λ (x :-: σ) xTerm) (Λ (y :-: τ) yTerm) context
        = notCrossBound && typesEquivalent σ τ context && αEquiv xTerm yTerm ((x, y) : context)
        where
            yFreeInX = y `elem` freeVariables xTerm
            xFreeInY = x `elem` freeVariables yTerm
            notCrossBound = x == y || (not yFreeInX && not xFreeInY)

    αEquiv (ΛT x xTerm) (ΛT y yTerm) context
        = notCrossBound && αEquiv xTerm yTerm ((x, y) : context)
        where
            yFreeInX = y `elem` freeVariables xTerm
            xFreeInY = x `elem` freeVariables yTerm
            notCrossBound = x == y || (not yFreeInX && not xFreeInY)

    αEquiv (App x1 x2) (App y1 y2) context = αEquiv x1 y1 context && αEquiv x2 y2 context
    αEquiv _ _ _ = False

    renameVariable :: Λ -> VariableName Λ -> VariableName Λ -> Λ
    renameVariable (Var (x :-: σ)) old new
        | x == old = Var (new :-: renameType σ old new)
        | otherwise = Var (x :-: renameType σ old new)
    renameVariable (Λ (x :-: σ) term) old new
        | x == old = Λ (new :-: renameType σ old new) $ renameVariable term old new
        | otherwise = Λ (x :-: renameType σ old new) $ renameVariable term old new
    renameVariable (ΛT p term) old new
        | p == old = ΛT new $ renameVariable term old new
        | otherwise = ΛT p $ renameVariable term old new
    renameVariable (App x y) old new = App (renameVariable x old new) (renameVariable y old new)

    prepareSubstitution :: Λ -> VariableName Λ -> Λ
    prepareSubstitution (Λ (x :-: σ) term) var
        | x /= var = Λ (x :-: makeTypeSafeFor σ var) $ prepareSubstitution term var
        | otherwise = Λ (newName :-: makeTypeSafeFor σ var) $ prepareSubstitution (renameVariable term x newName) var
        where newName = "_" ++ var
    prepareSubstitution (ΛT p term) var
        | p /= var = ΛT p $ prepareSubstitution term var
        | otherwise = ΛT newName $ prepareSubstitution (renameVariable term p newName) var
        where newName = "_" ++ var
    prepareSubstitution (App x y) var = App (prepareSubstitution x var) (prepareSubstitution y var)
    prepareSubstitution (Var (x :-: σ)) var = Var (x :-: makeTypeSafeFor σ var)

    performSubstitute :: Λ -> VariableName Λ -> Λ -> Maybe Λ
    performSubstitute (Var (x :-: σ)) var term
        | x /= var = Just $ Var (x :-: σ)
        | typeOf term /= Just σ = Nothing
        | otherwise = Just term
    performSubstitute (Λ (x :-: σ) t) var term
        | x /= var = Λ (x :-: σ) <$> performSubstitute t var term
        | otherwise = Just $ Λ (x :-: σ) t
    performSubstitute (ΛT p t) var term
        | p /= var = ΛT p <$> performSubstitute t var term
        | otherwise = Just $ ΛT p t
    performSubstitute (App x y) var term = App <$> performSubstitute x var term <*> performSubstitute y var term

    βReductions :: Λ -> [Λ]
    βReductions (App (Λ (x :-: σ) term) n) = [fromJust substitution | isJust substitution ] ++ reduceTerm ++ reduceApp
        where
            reduceTerm = (\newTerm -> App (Λ (x :-: σ) newTerm) n) <$> βReductions term
            reduceApp = App (Λ (x :-: σ) term) <$> βReductions n
            substitution = substitute term x n
    βReductions (App (ΛT p term) (Var (q :-: Type))) = substitution : reduceTerm
        where
            reduceTerm = (\newTerm -> App (ΛT p newTerm) (Var (q :-: Type))) <$> βReductions term
            substitution = substituteTypes term p (Pure q)
    βReductions (Var _) = []
    βReductions (Λ x term) = Λ x <$> βReductions term
    βReductions (ΛT p term) = ΛT p <$> βReductions term
    βReductions (App x y) = ((`App` y) <$> βReductions x) ++ (App x <$> βReductions y)

instance TypedΛCalculus Λ where
    data Type Λ = Pure (VariableName Λ) | (Type Λ) :-> (Type Λ) | Forall (VariableName Λ) (Type Λ) | Perp | Null | Type
        deriving (Show, Ord)

    prettyType :: Type Λ -> String
    prettyType (Pure σ) = σ
    prettyType (σ@(Pure _) :-> τ) = prettyType σ ++ "->" ++ prettyType τ
    prettyType (σ :-> τ) = "(" ++ prettyType σ ++ ")->" ++ prettyType τ
    prettyType (Forall p σ) = "∀" ++ p ++ "." ++ prettyType σ
    prettyType Null = "?"
    prettyType Perp = "⟂"
    prettyType Type = error "Invalid"

    typesEquivalent :: Type Λ -> Type Λ -> EquivalenceContext Λ -> Bool
    typesEquivalent (Pure σ) (Pure τ) context = σ == τ || (σ, τ) `elem` context
    typesEquivalent (σ :-> σ') (τ :-> τ') context = typesEquivalent σ τ context && typesEquivalent σ' τ' context
    typesEquivalent (Forall p σ) (Forall q τ) context
        = notCrossBound && typesEquivalent σ τ ((p, q) : context)
        where
            qFreeInΣ = q `elem` freeTypeVariables σ
            pFreeInτ = p `elem` freeTypeVariables τ
            notCrossBound = p == q || (not qFreeInΣ && not pFreeInτ)
    typesEquivalent Perp Perp _ = True
    typesEquivalent Type Type _ = True
    typesEquivalent _ _ _ = False

    typeOf :: Λ -> Maybe (Type Λ)
    typeOf (Var (_ :-: σ)) = Just σ
    typeOf (Λ (_ :-: σ) term) = (σ :->) <$> typeOf term
    typeOf (ΛT p term) = Forall p <$> typeOf term
    typeOf (App x (Var (y :-: Type)))
        = forallType =<< typeOf x
        where
            forallType :: Type Λ -> Maybe (Type Λ)
            forallType (Forall p t) = Just $ substituteType t p (Pure y)
            forallType _ = Nothing

    typeOf (App x y)
        = join $ functionType <$> typeOf x <*> typeOf y
        where
            functionType :: Type Λ -> Type Λ -> Maybe (Type Λ)
            functionType (σ :-> τ) υ | σ == υ = Just τ
            functionType _ _ = Nothing

    renameType :: Type Λ -> VariableName Λ -> VariableName Λ -> Type Λ
    renameType (Pure σ) old new
        | σ /= old = Pure σ
        | otherwise = Pure new
    renameType (x :-> y) old new = renameType x old new :-> renameType y old new
    renameType (Forall p τ) old new
        | p /= old = Forall p $ renameType τ old new
        | p == old = Forall p τ
    renameType σ _ _ = σ

    deduceTypes :: Λ -> TypeMapping Λ -> Λ
    deduceTypes (Var (x :-: Null)) types
        | isJust mapping = Var (x :-: fromJust mapping)
        | otherwise = Var (x :-: Null)
        where mapping = lookupSet x types
    deduceTypes (Var x) _ = Var x
    deduceTypes (Λ (x :-: σ) t) types = Λ (x :-: σ) $ deduceTypes t $ insert (x, σ) types
    deduceTypes (ΛT p t) types = ΛT p $ deduceTypes t $ insert (p, Type) types
    deduceTypes (App xTerm (Var (x :-: Null))) types
        | not isFunction && not isForall = App deduceX (Var (x :-: Null))
        | isFunction && isNothing mappedType = App deduceX (Var (x :-: σ))
        | isFunction && fromJust mappedType == σ = App deduceX (Var (x :-: σ))
        | isForall && isNothing mappedType = App deduceX (Var (x :-: Type))
        | isForall && fromJust mappedType == Type = App deduceX (Var (x :-: Type))
        | otherwise = App deduceX (Var (x :-: Null))
        where
            mappedType = lookupSet x types
            functionType = typeOf deduceX
            isFunction = isJust functionType && case fromJust functionType of
                                                    (_ :-> _) -> True
                                                    _ -> False
            Just (σ :-> _) = functionType
            isForall = isJust functionType && case fromJust functionType of
                                                    Forall _ _ -> True
                                                    _ -> False
            deduceX = deduceTypes xTerm types

    deduceTypes (App x y) types = App (deduceTypes x types) (deduceTypes y types)

    hasValidType :: Λ -> TypeMapping Λ -> Bool
    hasValidType (Var (x :-: σ)) vars = (x, σ) `elem` vars
    hasValidType (Λ (x :-: σ) term) vars = hasValidType term (insert (x, σ) $ Data.Set.filter (\(y, _) -> x /= y) vars)
    hasValidType (ΛT p term) vars = hasValidType term (insert (p, Type) $ Data.Set.filter (\(y, _) -> p /= y) vars)
    hasValidType t@(App x y) vars = hasValidType x vars && hasValidType y vars && isJust (typeOf t)


class ΛParameters a where
  toΛparameters :: [Variable Λ] -> a

instance ΛParameters (Λ -> Λ) where
  toΛparameters [] = error "No Λ parameters supplied"
  toΛparameters [x] = Λ x
  toΛparameters (x:xs) = Λ x . toΛparameters xs

instance (ΛParameters a) => ΛParameters (ΛVariable -> a) where
  toΛparameters xs x = toΛparameters (xs ++ [x])

instance (ΛParameters a) => ΛParameters (TypeableVariable -> a) where
  toΛparameters xs x = toΛparameters (xs ++ [toVariable x])

λ, l :: ΛParameters a => a
l = λ
λ = toΛparameters []

class ΛTypeParameters a where
  toTypeParameters :: [VariableName Λ] -> a

instance ΛTypeParameters (Λ -> Λ) where
  toTypeParameters [] = error "No ΛT parameters supplied"
  toTypeParameters [x] = ΛT x
  toTypeParameters (x:xs) = ΛT x . toTypeParameters xs

instance (ΛTypeParameters a) => ΛTypeParameters (String -> a) where
  toTypeParameters xs x = toTypeParameters (xs ++ [x])

λT, lT :: ΛTypeParameters a => a
lT = λT
λT = toTypeParameters []

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
a --> b = deduceTypes (a (toΛ b)) empty
infixr 5 -->

($$) :: (ΛTerm a, ΛTerm b) => a -> b -> Λ
x $$ y = App (toΛ x) (toΛ y)
infixl 6 $$

data TypeableVariable where
  (:::) :: Typeable a => VariableName Λ -> a -> TypeableVariable
infixl 6 :::

toVariable :: TypeableVariable -> Variable Λ
toVariable (x ::: t) = x :-: toType t

freeTypeVariables :: Type Λ -> Set (VariableName Λ)
freeTypeVariables (Pure x) = singleton x
freeTypeVariables (x :-> y) = freeTypeVariables x `union` freeTypeVariables y
freeTypeVariables (Forall x t) = delete x $ freeTypeVariables t
freeTypeVariables Perp = empty
freeTypeVariables Null = empty
freeTypeVariables Type = empty

makeTypeSafeFor :: Type Λ -> VariableName Λ -> Type Λ
makeTypeSafeFor (x :-> y) var = makeTypeSafeFor x var :-> makeTypeSafeFor y var
makeTypeSafeFor (Forall p t) var
 | p /= var = Forall p $ makeTypeSafeFor t var
 | otherwise = Forall newName $ makeTypeSafeFor (renameType t p newName) var
 where newName = "_" ++ var
makeTypeSafeFor t _ = t

substituteType :: Type Λ -> VariableName Λ -> Type Λ -> Type Λ
substituteType (Pure x) var t
 | x /= var = Pure x
 | otherwise = t
substituteType (x :-> y) var t = substituteType x var t :-> substituteType y var t
substituteType (Forall p x) var t
 | p /= var = Forall p $ substituteType x var t
 | otherwise = Forall p x
substituteType x _ _ = x

substituteTypes :: Λ -> VariableName Λ -> Type Λ -> Λ
substituteTypes (Var (x :-: s)) var t = Var (x :-: substituteType s var t)
substituteTypes (Λ (x :-: s) term) var t = Λ (x :-: substituteType s var t) $ substituteTypes term var t
substituteTypes (ΛT p term) var t
 | p /= var = ΛT p $ substituteTypes term var t
 | otherwise = ΛT p term
substituteTypes (App x y) var t = App (substituteTypes x var t) (substituteTypes y var t)

\end{code}
