module Quantum where
import Data.Complex
import Data.List

data A =  One -- 1
        | Sum A B -- a + b
        | Prod A B -- a * b
        | Rec [A] -- [a]
        | TypeError String
        deriving(Eq,Show)
type B = A


data T = Iso A B -- a<-->b
        | Comp A B T -- (a<-->b)-->T
        | IsoError String
        deriving(Eq,Show)
data V =  EmptyV
        | Xval String
        | InjL V
        | InjR V
        | PairV V V
        deriving(Eq,Show)
data P =  EmptyP
        | Xprod String
        | PairP P P
        deriving(Eq,Show)
data E =  Val V
        | LetE P Iso P E
        deriving(Eq,Show)

data Iso = Lambda String Iso
        | IsoVar String
        | App Iso Iso
        | Pattern [(V,E)]
        deriving(Eq,Show)

data Term = EmptyTerm
        | XTerm String
        | InjLt Term
        | InjRt Term
        | PairTerm Term Term
        | Omega Iso Term
        | Let P Term Term
        deriving(Eq,Show)

data TypeErrors = VarError String String
        | SumError String Term
        | ProdError String Term
        deriving(Show)

type Alpha = Complex 

--data E = Let P Phi P E 

type Delta = [(String,A)]
type Psi = [(String,T)]



-- Definição da Ortogonalidade de valores
(@@) :: V -> V -> Bool
(InjL v1) @@ (InjR v2) = True
(InjR v1) @@ (InjL v2) = True
(InjL v1) @@ (InjL v2) = v1 @@ v2
(InjR v1) @@ (InjR v2) = v1 @@ v2
(PairV v v1) @@ (PairV v' v2) = v1 @@ v2
-- (PairV v1 v) @@ (PairV v2 v') = v1 @@ v2 Por que esta definição existe?


wrap :: Either TypeErrors a -> a
wrap (Left err) = error (show err)
wrap (Right val) = val

mytermTypeCheck :: Delta -> Psi -> Term -> A -> Either TypeErrors A
mytermTypeCheck delta psi EmptyTerm a = Right One
mytermTypeCheck delta psi (XTerm x) a = Right (compareTypes a $ wrap $ myxType x $ xInContext x delta)
mytermTypeCheck delta psi (InjLt t) (Sum a b) = Right $ Sum (compareTypes a t $ wrap $ mytermTypeCheck delta psi t a) b



myxType :: String -> Maybe A -> Either TypeErrors A
myxType _ (Just v) = Right v -- Found the variable in the context, return its type
myxType x Nothing = Left $ VarError "Variable not in context: " x

xType :: Maybe A -> A
xType (Just v) = v -- Found the variable in the context, return its type
xType Nothing = TypeError "Variable not in context" 

xInContext :: String -> Delta -> Maybe A
xInContext x delta = lookup x delta -- Lookup a -> [(a,b)] -> Maybe b
                                    -- Returns b if it finds a pair based on provided key a

fType :: Maybe T -> T --Instead of building typeclasses for the Context Lookup function instances, create a new one
fType (Just t) = t
fType Nothing = IsoError "Function not in context"

fInContext :: String -> Psi -> Maybe T
fInContext f psi = lookup f psi

compareTypes :: A -> Term -> B -> B
compareTypes One t One = One
compareTypes a t b
        | a == b = a
        | otherwise = TypeError "SumTypes differ on term: " t

--(.) :: (b -> c) -> (a -> b) -> a -> c
valueTypeCheck ::  Delta -> V -> A  -> A
valueTypeCheck delta EmptyV One = One
valueTypeCheck delta (Xval x) a =  xType $ xInContext x delta 
valueTypeCheck delta (InjL v) (Sum a b) = valueTypeCheck delta v b
valueTypeCheck delta (InjR v) (Sum a b) = valueTypeCheck delta v a 
valueTypeCheck delta (PairV v v2) (Prod a b) = Prod  (valueTypeCheck delta v a) $ valueTypeCheck delta v2 b
-- Sums [(Alpha,V)]

termTypeCheck :: Delta -> Psi -> Term -> A -> A
termTypeCheck delta psi EmptyTerm a = One
termTypeCheck delta psi (XTerm x) a = compareTypes a $ xType $ xInContext x delta
termTypeCheck delta psi (InjLt t) (Sum a b) = Sum (compareTypes a $ termTypeCheck delta psi t a) b
termTypeCheck delta psi (InjRt t) (Sum a b) = Sum a (compareTypes b $ termTypeCheck delta psi t b)
termTypeCheck delta psi (PairTerm t1 t2) (Prod a b) = Prod (termTypeCheck delta psi t1 a) $ termTypeCheck delta psi t2 b
            --On pairs: differentiate the contexts for each t. Is it necessary?
termTypeCheck delta psi (Omega f t) b = termTypeCheck delta psi t $ checkIsoReturnType b $ isoTypeCheck psi f (Iso One b)
termTypeCheck delta psi (Let p t1 t2) c = let newDelta = fillPairTypes delta p $ termTypeCheck delta psi t1 c
                                            in termTypeCheck newDelta psi t2 c


fillPairTypes :: Delta-> P -> A -> Delta
fillPairTypes delta (PairP (Xprod x) (Xprod y)) (Prod a b) = delta ++ [(x,a),(y,b)]
fillPairTypes _ _ _ = error "Not expected operation" 

checkIsoReturnType ::  B -> T -> B
checkIsoReturnType b (Iso a b') = if b' == b then a
                                             else TypeError "Iso input type doesnt match Term"
checkIsoReturnType b _ = TypeError "Iso is not a function" 



isoTypeCheck :: Psi -> Iso -> T -> T
isoTypeCheck psi (IsoVar f) t = fType $ fInContext f psi
isoTypeCheck psi (Lambda f iso) t =  isoTypeCheck (addIsoNameToPsi psi (IsoVar f) $ breakIsoType t) iso (snd $ breakIsoType t)
isoTypeCheck _ _ _= IsoError "Cant typeCheck"

addIsoNameToPsi :: Psi -> Iso -> (T,T) -> Psi
addIsoNameToPsi psi (IsoVar f) types = (f,fst types) : psi

breakIsoType :: T -> (T,T)
breakIsoType (Comp a b t) = (Iso a b , t)
breakIsoType _ = error "Iso is not a computation"

{-
checkIso :: Psi -> Iso -> B -> A
checkIso psi iso b = isoInputTypeTest b $ isoType psi iso 

isoInputTypeTest :: B -> T -> A
isoInputTypeTest c (Iso a b)  
    | b == c    = a
    | otherwise = TypeError "Iso output doesnt match"

isoType :: Psi -> Iso -> T
isoType psi iso = filter ((==iso).fst) psi 

-}
