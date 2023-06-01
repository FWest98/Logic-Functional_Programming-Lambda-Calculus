\begin{code}

-- aka System F

module PolymorphicLambda (
    ΛP, LambdaP,
    λP, lP, λPT, lPT, (-->), ($$),
    PType (Forall), (==>), TypeableVariable((:::)),
    prettyΛP, prettyLambdaP, prettyPType,
    showΛP, showLambdaP, showPType, showTypeΛP, showTypeLambdaP,
    freeVariables, freeTypeVariables, substitute,
    isNormalForm, βReductions, betaReductions, normalForm, (===),
    deduceTypes, typeOf
) where

-- Imports
import Data.Set (Set, delete, singleton, union, empty, toList, insert, filter)
import Control.Monad
import Data.Maybe
import Debug.Trace (trace)

type VariableName = String
data PType = Pure VariableName | PType :-> PType | Forall VariableName PType | Perp | Null | Type
  deriving (Show, Ord)
data Variable = VariableName :-: PType
  deriving (Show, Eq, Ord)
data ΛP = Var Variable | ΛP Variable ΛP | ΛPT VariableName ΛP | App ΛP ΛP
  deriving (Show)
type LambdaP = ΛP

infixr 7 :->
infixl 6 :-:

type EquivalenceContext = [(VariableName, VariableName)]

equivalentTypes :: PType -> PType -> EquivalenceContext -> Bool
equivalentTypes (Pure x) (Pure y) context = x == y || (x, y) `elem` context
equivalentTypes (x :-> x') (y :-> y') context = equivalentTypes x y context && equivalentTypes x' y' context
equivalentTypes (Forall x xTerm) (Forall y yTerm) context
  = canSubstitute && equivalentTypes xTerm yTerm ((x, y) : context)
  where
    xInYterm = y `elem` freeTypeVariables xTerm
    yInXterm = x `elem` freeTypeVariables yTerm
    canSubstitute = x == y || (not yInXterm && not xInYterm)
equivalentTypes Perp Perp _ = True
equivalentTypes Type Type _ = True
equivalentTypes _ _ _ = False

instance Eq PType where
  x == y = equivalentTypes x y []

αEquiv :: ΛP -> ΛP -> EquivalenceContext -> Bool
αEquiv (Var (x :-: σ)) (Var (y :-: τ)) context
    = equivalentTypes σ τ context && (x == y || (x, y) `elem` context)

αEquiv (ΛP (x :-: σ) xTerm) (ΛP (y :-: τ) yTerm) context
  = canSubstitute && equivalentTypes σ τ context && αEquiv xTerm yTerm ((x, y) : context)
  where
    xInYterm = y `elem` freeVariables xTerm
    yInXterm = x `elem` freeVariables yTerm
    canSubstitute = x == y || (not yInXterm && not xInYterm)

αEquiv (ΛPT x xTerm) (ΛPT y yTerm) context
  = canSubstitute && αEquiv xTerm yTerm ((x, y) : context)
  where
    xInYterm = y `elem` freeVariables xTerm
    yInXterm = x `elem` freeVariables yTerm
    canSubstitute = x == y || (not yInXterm && not xInYterm)

αEquiv (App x1 x2) (App y1 y2) context = αEquiv x1 y1 context && αEquiv x2 y2 context
αEquiv _ _ _ = False

instance Eq ΛP where
  x == y = αEquiv x y []

class ΛPParams a where
  toΛPparams :: [Variable] -> a

instance ΛPParams (ΛP -> ΛP) where
  toΛPparams [] = error "No ΛP parameters supplied"
  toΛPparams [x] = ΛP x
  toΛPparams (x:xs) = ΛP x . toΛPparams xs

instance (ΛPParams a) => ΛPParams (Variable -> a) where
  toΛPparams xs x = toΛPparams (xs ++ [x])

instance (ΛPParams a) => ΛPParams (TypeableVariable -> a) where
  toΛPparams xs x = toΛPparams (xs ++ [toVariable x])

λP, lP :: ΛPParams a => a
lP = λP
λP = toΛPparams []

class ΛPTParams a where
  toΛPTparams :: [VariableName] -> a

instance ΛPTParams (ΛP -> ΛP) where
  toΛPTparams [] = error "No ΛPT parameters supplied"
  toΛPTparams [x] = ΛPT x
  toΛPTparams (x:xs) = ΛPT x . toΛPTparams xs

instance (ΛPTParams a) => ΛPTParams (VariableName -> a) where
  toΛPTparams xs x = toΛPTparams (xs ++ [x])

λPT, lPT :: ΛPTParams a => a
lPT = λPT
λPT = toΛPTparams []

class Typeable a where
  toPType :: a -> PType

instance Typeable PType where toPType = id
instance Typeable String where toPType = Pure

(==>) :: (Typeable a, Typeable b) => a -> b -> PType
a ==> b = toPType a :-> toPType b
infixr 7 ==>

class ΛPable a where
  toΛP :: a -> ΛP

instance ΛPable ΛP where toΛP = id
instance ΛPable VariableName where toΛP s = Var (s :-: Null)
instance ΛPable TypeableVariable where toΛP = Var . toVariable

(-->) :: ΛPable a => (ΛP -> ΛP) -> a -> ΛP
a --> b = deduceTypes (a (toΛP b)) empty
infixr 5 -->

($$) :: (ΛPable a, ΛPable b) => a -> b -> ΛP
x $$ y = App (toΛP x) (toΛP y)
infixl 6 $$

data TypeableVariable where
  (:::) :: Typeable a => VariableName -> a -> TypeableVariable
infixl 6 :::

toVariable :: TypeableVariable -> Variable
toVariable (x ::: t) = x :-: toPType t

prettyPType :: PType -> String
prettyPType (Pure t) = t
prettyPType (s@(Pure _) :-> t) = prettyPType s ++ "->" ++ prettyPType t
prettyPType (s :-> t) = "(" ++ prettyPType s ++ ")->" ++ prettyPType t
prettyPType (Forall s t) = "∀" ++ s ++ "." ++ prettyPType t
prettyPType Null = "?"
prettyPType Perp = "⟂"
prettyPType Type = error "Invalid"

prettyΛP, prettyLambdaP :: ΛP -> String
prettyLambdaP = prettyΛP
prettyΛP (Var (x :-: Null)) = x
prettyΛP (Var (x :-: Type)) = x
prettyΛP (Var (x :-: s)) = "(" ++ x ++ ":" ++ prettyPType s ++ ")"
prettyΛP (ΛP (x :-: s) term@(ΛP _ _)) = "λ" ++ x ++ ":" ++ prettyPType s ++ "," ++ tail (prettyΛP term)
prettyΛP (ΛP (x :-: s) term) = "λ" ++ x ++ ":" ++ prettyPType s ++ "." ++ prettyΛP term
prettyΛP (ΛPT x term@(ΛPT _ _)) = "Λ" ++ x ++ "," ++ tail (prettyΛP term)
prettyΛP (ΛPT x term) = "Λ" ++ x ++ prettyΛP term
prettyΛP (App x@(ΛP _ _) y@(Var _)) = "(" ++ prettyΛP x ++ ")" ++ prettyΛP y
prettyΛP (App x@(ΛP _ _) y) = "(" ++ prettyΛP x ++ ")(" ++ prettyΛP y ++ ")"
prettyΛP (App x@(ΛPT _ _) y@(Var _)) = "(" ++ prettyΛP x ++ ")" ++ prettyΛP y
prettyΛP (App x@(ΛPT _ _) y) = "(" ++ prettyΛP x ++ ")(" ++ prettyΛP y ++ ")"
prettyΛP (App x y@(Var _)) = prettyΛP x ++ prettyΛP y
prettyΛP (App x y) = prettyΛP x ++ "(" ++ prettyΛP y ++ ")"

showΛP, showLambdaP :: ΛP -> IO ()
showLambdaP = showΛP
showΛP = putStrLn . prettyΛP

showPType :: PType -> IO ()
showPType = putStrLn . prettyPType

showTypeΛP, showTypeLambdaP :: ΛP -> IO ()
showTypeLambdaP = showTypeΛP
showTypeΛP t = putStrLn $ maybe "Impossible type" prettyPType (typeOf t)

freeVariables :: ΛP -> Set VariableName
freeVariables (Var (x :-: t)) = singleton x `union` freeTypeVariables t
freeVariables (ΛP (x :-: _) term) = delete x $ freeVariables term
freeVariables (ΛPT x term) = delete x $ freeVariables term
freeVariables (App x y) = freeVariables x `union` freeVariables y

freeTypeVariables :: PType -> Set VariableName
freeTypeVariables (Pure x) = singleton x
freeTypeVariables (x :-> y) = freeTypeVariables x `union` freeTypeVariables y
freeTypeVariables (Forall x t) = delete x $ freeTypeVariables t
freeTypeVariables Perp = empty
freeTypeVariables Null = empty
freeTypeVariables Type = empty

type TypeMapping = Set (VariableName, PType)

lookupSet :: Eq a => a -> Set (a, b) -> Maybe b
lookupSet key = lookup key . toList

isValid :: ΛP -> TypeMapping -> Bool
isValid (Var (x :-: s)) vars = (x, s) `elem` vars
isValid (ΛP (x :-: s) term) vars = isValid term (insert (x, s) $ Data.Set.filter (\(y, _) -> x /= y) vars)
isValid (ΛPT p term) vars = isValid term (insert (p, Type) $ Data.Set.filter (\(y, _) -> p /= y) vars)
isValid t@(App x y) vars = isValid x vars && isValid y vars && isJust (typeOf t)

typeOf :: ΛP -> Maybe PType
typeOf (Var (_ :-: s)) = Just s
typeOf (ΛP (_ :-: s) term) = (s :->) <$> typeOf term
typeOf (ΛPT p term) = Forall p <$> typeOf term
typeOf (App x (Var (y :-: Type)))
  = forallType =<< typeOf x
  where
    forallType :: PType -> Maybe PType
    forallType (Forall p t) = Just $ substituteType t p (Pure y)
    forallType _ = Nothing

typeOf (App x y)
  = join $ functionType <$> typeOf x <*> typeOf y
  where
    functionType :: PType -> PType -> Maybe PType
    functionType (s :-> t) u | s == u = Just t
    --functionType (Forall p t) Type = Just $ substituteType t p (Pure "q")
    functionType _ _ = Nothing

deduceTypes :: ΛP -> TypeMapping -> ΛP
--deduceTypes term types | trace ("DEBUG:  " ++ show term ++ "   -------   " ++ show types) False = undefined
deduceTypes (Var (x :-: Null)) types
                                | isJust mapping = Var (x :-: fromJust mapping)
                                | otherwise = Var (x :-: Null)
                            where mapping = lookupSet x types
deduceTypes (Var x) _ = Var x
deduceTypes (ΛP (x :-: s) t) types = ΛP (x :-: s) $ deduceTypes t $ insert (x, s) types
deduceTypes (ΛPT p t) types = ΛPT p $ deduceTypes t $ insert (p, Type) types
deduceTypes (App xTerm (Var (x :-: Null))) types
  | not isFunction && not isForall = App deduceX (Var (x :-: Null))
  | isFunction && isNothing mappedType = App deduceX (Var (x :-: s))
  | isFunction && fromJust mappedType == s = App deduceX (Var (x :-: s))
  | isForall && isNothing mappedType = App deduceX (Var (x :-: Type))
  | isForall && fromJust mappedType == Type = App deduceX (Var (x :-: Type))
  | otherwise = trace ("DEBUGEXTRA  |||||| " ++ show xTerm ++ "   " ++ show functionType ++ "   " ++ show mappedType ++ " ||||||") $ App deduceX (Var (x :-: Null))
 where
  mappedType = lookupSet x types
  functionType = typeOf deduceX
  isFunction = isJust functionType && case fromJust functionType of
                                          (_ :-> _) -> True
                                          _ -> False
  Just (s :-> _) = functionType
  isForall = isJust functionType && case fromJust functionType of
                                          Forall _ _ -> True
                                          _ -> False
  deduceX = deduceTypes xTerm types

deduceTypes (App x y) types = App (deduceTypes x types) (deduceTypes y types)

substitute :: ΛP -> VariableName -> ΛP -> Maybe ΛP
substitute (Var (x :-: s)) var term
                          | x /= var = Just $ Var (x :-: s)
                          | typeOf term /= Just s = Nothing
                          | otherwise = Just term
substitute (ΛP (x :-: s) t) var term
                          | x /= var = ΛP (x :-: s) <$> substitute t var term
                          | otherwise = Just $ ΛP (x :-: s) t
substitute (ΛPT x t) var term
                          | x /= var = ΛPT x <$> substitute t var term
                          | otherwise = Just $ ΛPT x t
substitute (App x y) var term = App <$> substitute x var term <*> substitute y var term

substituteType :: PType -> VariableName -> PType -> PType
substituteType (Pure x) var t
 | x /= var = Pure x
 | otherwise = t
substituteType (x :-> y) var t = substituteType x var t :-> substituteType y var t
substituteType (Forall p x) var t
 | p /= var = Forall p $ substituteType x var t
 | otherwise = Forall p x
substituteType x _ _ = x

substituteTypes :: ΛP -> VariableName -> PType -> ΛP
substituteTypes (Var (x :-: s)) var t = Var (x :-: substituteType s var t)
substituteTypes (ΛP (x :-: s) term) var t = ΛP (x :-: substituteType s var t) $ substituteTypes term var t
substituteTypes (ΛPT p term) var t
 | p /= var = ΛPT p $ substituteTypes term var t
 | otherwise = ΛPT p term
substituteTypes (App x y) var t = App (substituteTypes x var t) (substituteTypes y var t)

hasβRedex :: ΛP -> Bool
hasβRedex (App (ΛP _ _) t) = typeOf t /= Just Type
hasβRedex (App (ΛPT _ _) t) = typeOf t == Just Type
hasβRedex (Var _) = False
hasβRedex (ΛP _ term) = hasβRedex term
hasβRedex (ΛPT _ term) = hasβRedex term
hasβRedex (App x y) = hasβRedex x || hasβRedex y

isNormalForm :: ΛP -> Bool
isNormalForm = null . βReductions

βReductions, betaReductions :: ΛP -> [ΛP]
betaReductions = βReductions
βReductions (App (ΛP (x :-: s) term) n) = [fromJust substitution | isJust substitution ] ++ reduceTerm ++ reduceApp
  where
    reduceTerm = (\newTerm -> App (ΛP (x :-: s) newTerm) n) <$> βReductions term
    reduceApp = App (ΛP (x :-: s) term) <$> βReductions n
    substitution = substitute term x n
βReductions (App (ΛPT p term) (Var (q :-: Type))) = substitution : reduceTerm
  where
    reduceTerm = (\newTerm -> App (ΛPT p newTerm) (Var (q :-: Type))) <$> βReductions term
    substitution = substituteTypes term p (Pure q)
βReductions (Var _) = []
βReductions (ΛP x term) = ΛP x <$> βReductions term
βReductions (ΛPT p term) = ΛPT p <$> βReductions term
βReductions (App x y) = ((`App` y) <$> βReductions x) ++ (App x <$> βReductions y)

βReduceLeft :: ΛP -> ΛP
βReduceLeft t
 | null reduction = error "The λ-term is already in normal form!"
 | otherwise = head reduction
 where reduction = take 1 $ βReductions t

normalForm :: ΛP -> ΛP
normalForm t | trace (prettyLambdaP t) False = undefined
normalForm t
 | isNormalForm t = t
 | otherwise = (normalForm . βReduceLeft) t

(===) :: ΛP -> ΛP -> Bool
x === y = x == y || normalForm x == normalForm y
infix 1 ===

\end{code}
