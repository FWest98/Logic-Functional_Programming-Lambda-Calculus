\begin{code}

module TypedLambda (
    ΛT, LambdaT,
    λT, lT, (-->), ($$), (==>), TypeableVariable((:::)),
    prettyΛT, prettyLambdaT, prettyType, showΛT, showLambdaT, showType, showTypeΛT, showTypeLambdaT,
    freeVariables, substitute,
    isNormalForm, βReductions, betaReductions, normalForm, (===)
) where

-- Imports
import Data.Maybe (isJust, fromJust, isNothing)
import Data.Set (Set, delete, union, singleton, insert, filter, toList)
import Control.Monad

type VariableName = String
data Type = Pure VariableName | Type :-> Type | Perp | Null
    deriving (Show, Eq, Ord)
data Variable = VariableName :-: Type
    deriving (Show, Eq, Ord)
data ΛT = Var Variable | ΛT Variable ΛT | App ΛT ΛT
    deriving (Show)
type LambdaT = ΛT

infixr 7 :->
infixl 6 :-:

type EquivalenceContext = [(VariableName, VariableName)]

αEquiv :: ΛT -> ΛT -> EquivalenceContext -> Bool
αEquiv (Var (x :-: σ)) (Var (y :-: τ)) context
    = σ == τ && (x == y || (x, y) `elem` context)

αEquiv (ΛT (x :-: σ) xTerm) (ΛT (y :-: τ) yTerm) context
  = canSubstitute && σ == τ && αEquiv xTerm yTerm ((x, y) : context)
  where
    xInYterm = y `elem` freeVariables xTerm
    yInXterm = x `elem` freeVariables yTerm
    canSubstitute = not yInXterm && not xInYterm

αEquiv (App x1 x2) (App y1 y2) context = αEquiv x1 y1 context && αEquiv x2 y2 context
αEquiv _ _ _ = False

instance Eq ΛT where
  x == y = αEquiv x y []

class ΛTParams a where
  toΛTparams :: [Variable] -> a

instance ΛTParams (ΛT -> ΛT) where
  toΛTparams [] = error "No ΛT parameters supplied"
  toΛTparams [x] = ΛT x
  toΛTparams (x:xs) = ΛT x . toΛTparams xs

instance (ΛTParams a) => ΛTParams (Variable -> a) where
  toΛTparams xs x = toΛTparams (xs ++ [x])

instance (ΛTParams a) => ΛTParams (TypeableVariable -> a) where
  toΛTparams xs x = toΛTparams (xs ++ [toVariable x])

λT, lT :: ΛTParams a => a
lT = λT
λT = toΛTparams []

class Typable a where
  toType :: a -> Type

instance Typable Type where toType = id
instance Typable VariableName where toType = Pure

(==>) :: (Typable a, Typable b) => a -> b -> Type
a ==> b = toType a :-> toType b
infixr 7 ==>

class ΛTable a where
  toΛT :: a -> ΛT

instance ΛTable ΛT where toΛT = id
instance ΛTable VariableName where toΛT s = Var (s :-: Null)
instance ΛTable TypeableVariable where toΛT = Var . toVariable

(-->) :: ΛTable a => (ΛT -> ΛT) -> a -> ΛT
a --> b = a (toΛT b)
infixr 5 -->

($$) :: (ΛTable a, ΛTable b) => a -> b -> ΛT
x $$ y = App (toΛT x) (toΛT y)
infixl 6 $$

data TypeableVariable where
  (:::) :: Typable a => VariableName -> a -> TypeableVariable
infixl 6 :::

toVariable :: TypeableVariable -> Variable
toVariable (x ::: σ) = x :-: toType σ

prettyType :: Type -> String
prettyType (Pure σ) = σ
prettyType (σ@(Pure _) :-> τ) = prettyType σ ++ "->" ++ prettyType τ
prettyType (σ :-> τ) = "(" ++ prettyType σ ++ ")->" ++ prettyType τ
prettyType Null = "?"
prettyType Perp = "⟂"

prettyΛT, prettyLambdaT :: ΛT -> String
prettyLambdaT = prettyΛT
prettyΛT (Var (x :-: Null)) = x
prettyΛT (Var (x :-: σ)) = "(" ++ x ++ ":" ++ prettyType σ ++ ")"
prettyΛT (ΛT (x :-: σ) term@(ΛT _ _)) = "λ" ++ x ++ ":" ++ prettyType σ ++ "," ++ tail (prettyΛT term)
prettyΛT (ΛT (x :-: σ) term) = "λ" ++ x ++ ":" ++ prettyType σ ++ "." ++ prettyΛT term
prettyΛT (App x@(ΛT _ _) y@(Var _)) = "(" ++ prettyΛT x ++ ")" ++ prettyΛT y
prettyΛT (App x@(ΛT _ _) y) = "(" ++ prettyΛT x ++ ")(" ++ prettyΛT y ++ ")"
prettyΛT (App x y@(Var _)) = prettyΛT x ++ prettyΛT y
prettyΛT (App x y) = prettyΛT x ++ "(" ++ prettyΛT y ++ ")"

showΛT, showLambdaT :: ΛT -> IO ()
showLambdaT = showΛT
showΛT = putStrLn . prettyΛT

showType :: Type -> IO ()
showType = putStrLn . prettyType

showTypeΛT, showTypeLambdaT :: ΛT -> IO ()
showTypeLambdaT = showTypeΛT
showTypeΛT t = putStrLn $ maybe "Impossible type" prettyType (typeOf t)

freeVariables :: ΛT -> Set VariableName
freeVariables (Var (x :-: _)) = singleton x
freeVariables (ΛT (x :-: _) term) = delete x $ freeVariables term
freeVariables (App x y) = freeVariables x `union` freeVariables y

type TypeMapping = Set (VariableName, Type)

lookupSet :: Eq a => a -> Set (a, b) -> Maybe b
lookupSet key = lookup key . toList

isValid :: ΛT -> TypeMapping -> Bool
isValid (Var (x :-: σ)) vars = (x, σ) `elem` vars
isValid (ΛT (x :-: σ) term) vars = isValid term (insert (x, σ) $ Data.Set.filter (\(y, _) -> x /= y) vars)
isValid t@(App x y) vars = isValid x vars && isValid y vars && isJust (typeOf t)

typeOf :: ΛT -> Maybe Type
typeOf (Var (_ :-: σ)) = Just σ
typeOf (ΛT (_ :-: σ) term) = (σ :->) <$> typeOf term
typeOf (App x y)
  = join $ functionType <$> typeOf x <*> typeOf y
  where
    functionType :: Type -> Type -> Maybe Type
    functionType (σ :-> τ) υ
     | σ == υ = Just τ
     | otherwise = Nothing
    functionType _ _ = Nothing

deduceTypes :: ΛT -> TypeMapping -> ΛT
deduceTypes (Var (x :-: Null)) types
                                | isJust mapping = Var (x :-: fromJust mapping)
                                | otherwise = Var (x :-: Null)
                            where mapping = lookupSet x types
deduceTypes (Var x) _ = Var x
deduceTypes (ΛT (x :-: σ) t) types = ΛT (x :-: σ) $ deduceTypes t $ insert (x, σ) types
deduceTypes (App xTerm (Var (x :-: Null))) types
    | not isFunction = App deduceX (Var (x :-: Perp))
    | isNothing mappedType = App deduceX (Var (x :-: σ))
    | fromJust mappedType == σ = App deduceX (Var (x :-: σ))
    | otherwise = App deduceX (Var (x :-: Perp))
  where
    mappedType = lookupSet x types
    functionType = typeOf deduceX
    isFunction = isJust functionType && case fromJust functionType of
                                            (_ :-> _) -> True
                                            _ -> False
    Just (σ :-> _) = functionType
    deduceX = deduceTypes xTerm types

deduceTypes (App x y) types = App (deduceTypes x types) (deduceTypes y types)

substitute :: ΛT -> VariableName -> ΛT -> Maybe ΛT
substitute (Var (x :-: σ)) var term
                          | x /= var = Just $ Var (x :-: σ)
                          | typeOf term /= Just σ = Nothing
                          | otherwise = Just term
substitute (ΛT (x :-: σ) t) var term
                          | x /= var = ΛT (x :-: σ) <$> substitute t var term
                          | otherwise = Just $ ΛT (x :-: σ) t
substitute (App x y) var term = App <$> substitute x var term <*> substitute y var term

hasβRedex :: ΛT -> Bool
hasβRedex (App (ΛT _ _) _) = True
hasβRedex (Var _) = False
hasβRedex (ΛT _ term) = hasβRedex term
hasβRedex (App x y) = hasβRedex x || hasβRedex y

isNormalForm :: ΛT -> Bool
isNormalForm = not . hasβRedex

βReductions, betaReductions :: ΛT -> [ΛT]
betaReductions = βReductions
βReductions (App (ΛT (x :-: σ) term) n) = [fromJust substitution | isJust substitution] ++ reduceTerm ++ reduceApp
  where
    reduceTerm = (\newTerm -> App (ΛT (x :-: σ) newTerm) n) <$> βReductions term
    reduceApp = App (ΛT (x :-: σ) term) <$> βReductions n
    substitution = substitute term x n
βReductions (Var _) = []
βReductions (ΛT x term) = ΛT x <$> βReductions term
βReductions (App x y) = ((`App` y) <$> βReductions x) ++ (App x <$> βReductions y)

βReduceLeft :: ΛT -> ΛT
βReduceLeft t
 | hasβRedex t = head $ βReductions t
 | otherwise = error "The λ-term is already in normal form!"

normalForm :: ΛT -> ΛT
normalForm t
 | isNormalForm t = t
 | otherwise = (normalForm . βReduceLeft) t

(===) :: ΛT -> ΛT -> Bool
x === y = x == y || normalForm x == normalForm y
infix 1 ===

\end{code}
