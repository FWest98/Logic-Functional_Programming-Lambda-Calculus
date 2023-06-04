\section{Polymorphic Λ-calculus a.k.a. System F}

The final implementation we provide is one for polymorphic $λ$-calculus, better known as System F. It allows for quantification over types as an extension of the simply-typed calculus we discussed above. Again, we will only focus on the interesting/unique aspects.

\ignore{
\begin{code}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}

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
\end{code}
}
\begin{code}
data ΛVariable = (VariableName Λ) :-: (Type Λ)
  deriving (Show, Eq, Ord)
infixl 6 :-:

data Λ = Var ΛVariable | Λ ΛVariable Λ | ΛT (VariableName Λ) Λ | App Λ Λ
  deriving (Show)
type Lambda = Λ
\end{code}
\vspace{-23pt}

These definitions are nearly identical to previous instances, except that our {\tt Λ} data type now has a fourth constructor for a quantification over a type parameter. The type parameter is represented by just a name. Another approach would have been to represent quantification over types by a lambda function with a parameter of a {\tt Type} type, but that would arguably lead to uglier code. In the current approach we do still need a {\tt Type} type, so that type variable usages are possible.

\begin{code}
instance Substitutable Λ String where
    freeVariables :: Λ -> Set (VariableName Λ)
    freeVariables (Var (x :-: σ))    = insert x $ freeVariables σ
    freeVariables (Λ (x :-: _) term) = delete x $ freeVariables term
    freeVariables (ΛT p term)        = delete p $ freeVariables term
    freeVariables (App x y)          = freeVariables x `union` freeVariables y
\end{code}
\vspace{-23pt}

Already in this simple function we see the first signs of what is the biggest complication of quantification over types: we are mixing types and terms. A type variable can occur inside a term, types now have free variables as well, so this greatly complicates our design. The types for our polymorphic calculus will therefore also be an instance of \hs!Substitutable!, since we need to be able to perform substitutions there as well.

\begin{code}
    renameVariable :: Λ -> VariableName Λ -> VariableName Λ -> Λ
    renameVariable (Var (x :-: σ)) old new
        | x == old  = Var (new :-: renameVariable σ old new)
        | otherwise = Var (x   :-: renameVariable σ old new)
    renameVariable (Λ (x :-: σ) term) old new
        | x == old  = Λ (new :-: renameVariable σ old new) $ renameVariable term old new
        | otherwise = Λ (x   :-: renameVariable σ old new) $ renameVariable term old new
    renameVariable (ΛT p term) old new
        | p == old  = ΛT new $ renameVariable term old new
        | otherwise = ΛT p   $ renameVariable term old new
    renameVariable (App x y) old new = App (renameVariable x old new) (renameVariable y old new)

    prepareSubstitution :: Λ -> VariableName Λ -> Λ
    prepareSubstitution (Λ (x :-: σ) term) var
        | x /= var  = Λ (x       :-: prepareSubstitution σ var) $ prepareSubstitution term var
        | otherwise = Λ (newName :-: prepareSubstitution σ var) $ prepareSubstitution (renameVariable term x newName) var
        where newName = "_" ++ var
    prepareSubstitution (ΛT p term) var
        | p /= var  = ΛT p       $ prepareSubstitution term var
        | otherwise = ΛT newName $ prepareSubstitution (renameVariable term p newName) var
        where newName = "_" ++ var
    prepareSubstitution (App x y) var = App (prepareSubstitution x var) (prepareSubstitution y var)
    prepareSubstitution (Var (x :-: σ)) var = Var (x :-: prepareSubstitution σ var)

    performSubstitution :: Λ -> VariableName Λ -> Λ -> Maybe Λ
    performSubstitution (Var (x :-: σ)) var term
        | x /= var              = Just $ Var (x :-: σ)
        | typeOf term /= Just σ = Nothing
        | otherwise             = Just term
    performSubstitution (Λ (x :-: σ) t) var term
        | x /= var  = Λ (x :-: σ) <$> performSubstitution t var term
        | otherwise = Just $ Λ (x :-: σ) t
    performSubstitution (ΛT p t) var term
        | p /= var  = ΛT p <$> performSubstitution t var term
        | otherwise = Just $ ΛT p t
    performSubstitution (App x y) var term = App <$> performSubstitution x var term <*> performSubstitution y var term
\end{code}
\vspace{-23pt}

Renaming here is still relatively straightforward - it just needs to be propagated to inside the types as well, the same holds for preparing a substitution. Performing one is a bit more challenging, since we now need to be more careful with the types. We also need to distinguish between applying a variable to a $λ$-term, or a $Λ$-term - the latter being quantification over types.

\begin{code}
instance ΛCalculus Λ where
    type Variable Λ = ΛVariable
\end{code}
\vspace{-23pt}

We omit pretty printing code for brevity

\ignore{
\begin{code}
    fromVar = Var
    fromVarName name = Var (name :-: Null)
    fromΛ = Λ
    fromApp = App

    prettyΛ :: Λ -> String
    prettyΛ (Var (x :-: Null))         = x
    prettyΛ (Var (x :-: Type))         = x
    prettyΛ (Var (x :-: σ))            = "(" ++ x ++ ":" ++ prettyType σ ++ ")"
    prettyΛ (Λ (x :-: σ) term@(Λ _ _)) = "λ" ++ x ++ ":" ++ prettyType σ ++ "," ++ tail (prettyΛ term)
    prettyΛ (Λ (x :-: σ) term)         = "λ" ++ x ++ ":" ++ prettyType σ ++ "." ++ prettyΛ term
    prettyΛ (ΛT x term@(ΛT _ _))       = "Λ" ++ x ++ "," ++ tail (prettyΛ term)
    prettyΛ (ΛT x term)                = "Λ" ++ x ++ prettyΛ term
    prettyΛ (App x@(Λ _ _)  y@(Var _)) = "(" ++ prettyΛ x ++ ")"  ++ prettyΛ y
    prettyΛ (App x@(Λ _ _)  y)         = "(" ++ prettyΛ x ++ ")(" ++ prettyΛ y ++ ")"
    prettyΛ (App x@(ΛT _ _) y@(Var _)) = "(" ++ prettyΛ x ++ ")"  ++ prettyΛ y
    prettyΛ (App x@(ΛT _ _) y)         = "(" ++ prettyΛ x ++ ")(" ++ prettyΛ y ++ ")"
    prettyΛ (App x          y@(Var _)) = prettyΛ x ++        prettyΛ y
    prettyΛ (App x          y)         = prettyΛ x ++ "(" ++ prettyΛ y ++ ")"
\end{code}
}

\begin{code}
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

    βReductions :: Λ -> [Λ]
    βReductions (App (Λ (x :-: σ) term) n) = [fromJust substitution | isJust substitution ] ++ reduceTerm ++ reduceApp
        where
            reduceTerm   = (\newTerm -> App (Λ (x :-: σ) newTerm) n) <$> βReductions term
            reduceApp    = App (Λ (x :-: σ) term) <$> βReductions n
            substitution = substitute term x n
    βReductions (App (ΛT p term) (Var (q :-: Type))) = [fromJust substitution | isJust substitution] ++ reduceTerm
        where
            reduceTerm   = (\newTerm -> App (ΛT p newTerm) (Var (q :-: Type))) <$> βReductions term
            substitution = substituteTypes term p (Pure q)
    βReductions (Var _)     = []
    βReductions (Λ x term)  = Λ x  <$> βReductions term
    βReductions (ΛT p term) = ΛT p <$> βReductions term
    βReductions (App x y)   = ((`App` y) <$> βReductions x) ++ (App x <$> βReductions y)
\end{code}
\vspace{-23pt}

The $α$-equivalence check is a bit more extensive with an additional case to check (type quantification) and a more sophisticated check for type equivalence. $β$-reductions might be the trickiest in this section, with a newly added type quantification, but even that follows the existing patterns that we already know.

\begin{code}
instance Substitutable (Type Λ) String where
    freeVariables :: Type Λ -> Set (VariableName Λ)
    freeVariables (Pure σ)     = singleton σ
    freeVariables (σ :-> τ)    = freeVariables σ `union` freeVariables τ
    freeVariables (Forall p τ) = delete p $ freeVariables τ
    freeVariables Perp         = empty
    freeVariables Null         = empty
    freeVariables Type         = empty

    renameVariable :: Type Λ -> VariableName Λ -> VariableName Λ -> Type Λ
    renameVariable (Pure σ)     old new
        | σ /= old  = Pure σ
        | otherwise = Pure new
    renameVariable (σ :-> τ)    old new = renameVariable σ old new :-> renameVariable τ old new
    renameVariable (Forall p τ) old new
        | p /= old = Forall p $ renameVariable τ old new
        | p == old = Forall p τ
    renameVariable σ _ _ = σ

    prepareSubstitution :: Type Λ -> VariableName Λ -> Type Λ
    prepareSubstitution (σ :-> τ) var = prepareSubstitution σ var :-> prepareSubstitution τ var
    prepareSubstitution (Forall p τ) var
        | p /= var  = Forall p $ prepareSubstitution τ var
        | otherwise = Forall newName $ prepareSubstitution (renameVariable τ p newName) var
        where newName = "_" ++ var
    prepareSubstitution σ _ = σ

    performSubstitution :: Type Λ -> VariableName Λ -> Type Λ -> Maybe (Type Λ)
    performSubstitution (Pure σ)     var term
        | σ /= var  = Just $ Pure σ
        | otherwise = Just term
    performSubstitution (σ :-> τ)    var term = (:->) <$> performSubstitution σ var term <*> performSubstitution τ var term
    performSubstitution (Forall p t) var term
        | p /= var  = Forall p <$> performSubstitution t var term
        | otherwise = Just $ Forall p t
    performSubstitution σ _ _ = Just σ

substituteTypes :: Λ -> VariableName Λ -> Type Λ -> Maybe Λ
substituteTypes (Var (x :-: σ)) var term = Var <$> ((x :-:) <$> substitute σ var term)
substituteTypes (Λ (x :-: σ) t) var term = Λ   <$> ((x :-:) <$> substitute σ var term) <*> substituteTypes t var term
substituteTypes (ΛT p t) var term
 | p /= var  = ΛT p <$> substituteTypes t var term
 | otherwise = Just $ ΛT p t
substituteTypes (App x y) var term = App <$> substituteTypes x var term <*> substituteTypes y var term
\end{code}
\vspace{-23pt}

Now we make sure that our type system (to be defined further down in the \hs!TypedΛCalculus! instance) allows substitution as well. The function implementations follow the patterns and conventions we have used before, just with different constructors and semantics. We do introduce a special function `bridging' between terms and types: allowing us to substitute a type directly everywhere in a term.

\begin{code}
infixr 7 :->
instance TypedΛCalculus Λ where
    data Type Λ = Pure (VariableName Λ) | (Type Λ) :-> (Type Λ) | Forall (VariableName Λ) (Type Λ) | Perp | Null | Type
        deriving (Show, Ord)
\end{code}
\vspace{-23pt}

The type system for our polymorphic calculus extends the simple types from before by adding a \hs!Forall! constructor - serving as quantification over tyeps. We do not introduce special syntax or notation for it, since writing out `forall' is already the most readable approach.

\begin{code}
    prettyType :: Type Λ -> String
    prettyType (Pure σ)           = σ
    prettyType (σ@(Pure _) :-> τ) = prettyType σ ++ "->" ++ prettyType τ
    prettyType (σ :-> τ)          = "(" ++ prettyType σ ++ ")->" ++ prettyType τ
    prettyType (Forall p σ)       = "∀" ++ p ++ "." ++ prettyType σ
    prettyType Null               = "?"
    prettyType Perp               = "⟂"
    prettyType Type               = error "Invalid"

    typesEquivalent :: Type Λ -> Type Λ -> EquivalenceContext Λ -> Bool
    typesEquivalent (Pure σ)     (Pure τ)     context = σ == τ || (σ, τ) `elem` context
    typesEquivalent (σ :-> σ')   (τ :-> τ')   context = typesEquivalent σ τ context && typesEquivalent σ' τ' context
    typesEquivalent (Forall p σ) (Forall q τ) context
        = notCrossBound && typesEquivalent σ τ ((p, q) : context)
        where
            qFreeInΣ = q `elem` freeVariables σ
            pFreeInτ = p `elem` freeVariables τ
            notCrossBound = p == q || (not qFreeInΣ && not pFreeInτ)
    typesEquivalent Perp Perp _ = True
    typesEquivalent Type Type _ = True
    typesEquivalent _    _    _ = False
\end{code}
\vspace{-23pt}

Pretty printing works as expected, but in this case we need the type equivalence to be more sophisticated than a simple built-in equality - since we should identify types of the same structure but with different bound variable names ($\forall p.p \to p \equiv \forall q.q \to q$). The structure is the same as for $α$-equivalence of $λ$-terms.

\begin{code}
    typeOf :: Λ -> Maybe (Type Λ)
    typeOf (Var (_ :-: σ))            = Just σ
    typeOf (Λ (_ :-: σ) term)         = (σ :->)  <$> typeOf term
    typeOf (ΛT p term)                = Forall p <$> typeOf term
    typeOf (App x (Var (y :-: Type))) = forallType =<< typeOf x
        where
            forallType :: Type Λ -> Maybe (Type Λ)
            forallType (Forall p t) = substitute t p (Pure y)
            forallType _            = Nothing

    typeOf (App x y)
        = join $ functionType <$> typeOf x <*> typeOf y
        where
            functionType :: Type Λ -> Type Λ -> Maybe (Type Λ)
            functionType (σ :-> τ) υ | σ == υ = Just τ
            functionType _ _ = Nothing
\end{code}
\vspace{-23pt}

The {\tt typeOf} function now has an additional code for quantification, where we need to check that it is only applied to `type variables' and not to any ordinary variable.

\begin{code}
    deduceTypes :: Λ -> TypeMapping Λ -> Λ
    deduceTypes (Var (x :-: Null)) types
        | isJust mapping = Var (x :-: fromJust mapping)
        | otherwise      = Var (x :-: Null)
        where mapping = lookupSet x types
    deduceTypes (Var x)         _     = Var x
    deduceTypes (Λ (x :-: σ) t) types = Λ (x :-: σ) $ deduceTypes t $ insert (x, σ) types
    deduceTypes (ΛT p t)        types = ΛT p $ deduceTypes t $ insert (p, Type) types
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
            Just (σ :-> _) = functionType -- This will generate a warning but is explicitly safe here
            isForall = isJust functionType && case fromJust functionType of
                                                    Forall _ _ -> True
                                                    _ -> False
            deduceX = deduceTypes xTerm types

    deduceTypes (App x y) types = App (deduceTypes x types) (deduceTypes y types)

    hasValidType :: Λ -> TypeMapping Λ -> Bool
    hasValidType (Var (x :-: σ))    vars = (x, σ) `elem` vars
    hasValidType (Λ (x :-: σ) term) vars = hasValidType term (insert (x, σ) $ Data.Set.filter (\(y, _) -> x /= y) vars)
    hasValidType (ΛT p term)        vars = hasValidType term (insert (p, Type) $ Data.Set.filter (\(y, _) -> p /= y) vars)
    hasValidType t@(App x y)        vars = hasValidType x vars && hasValidType y vars && isJust (typeOf t)
\end{code}
\vspace{-23pt}

The type deduction system is once again the most complicated part, but still looks very similar to existing cases. The only difference is that for applications, we need to check whether we are applying to a function or a quantification, and check the types of the arguments differently. This also applies to {\tt hasValidType}.

\subsection{Parsing}
The parsing is nearly entirely identical to the typed version - with the addition of an abstraction over types. For brevity, we will not repeat the code once again.

\ignore{
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

class ΛTerm a where
  toΛ :: a -> Λ

instance ΛTerm Λ                where toΛ = id
instance ΛTerm String           where toΛ = fromVarName
instance ΛTerm TypeableVariable where toΛ = Var . toVariable

(-->) :: ΛTerm a => (Λ -> Λ) -> a -> Λ
a --> b = deduceTypes (a (toΛ b)) empty
infixr 5 -->

($$) :: (ΛTerm a, ΛTerm b) => a -> b -> Λ
x $$ y = App (toΛ x) (toΛ y)
infixl 6 $$
\end{code}
}
