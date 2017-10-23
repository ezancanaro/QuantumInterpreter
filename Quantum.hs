module Quantum where
import Data.Complex
import Data.List

data A =  One -- 1
        | Sum A B -- a + b
        | Prod A B -- a * b
        | Rec [A] -- [a] List(A)= Sum One (Prod A List(A))
        | TypeError String
        deriving(Eq)
type B = A


data T = Iso A B -- a<-->b
        | Comp A B T -- (a<-->b)-->T
        deriving(Eq)
data V =  EmptyV
        | Xval String
        | InjL V
        | InjR V
        | PairV V V
        deriving(Eq,Show)
data P =  EmptyP
        | Xprod String --Equivale ao par <(),x>
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
        | ProdError String P
        | IsoError String String String
        | OmegaError String Term
        | AppError String Iso Iso
        | ValueError String V A
        | OrthogonalDecomp String [V]
        | CustomError String String
        deriving(Show)

type Alpha = Complex

--data E = Let P Phi P E

type Delta = [(String,A)]
type Psi = [(String,T)]
type OD = [V]
type ODext = [E]

instance Show (A) where
  show (One) = "1"
  show (Sum a b) = show a ++ "+" ++ show b
  show (Prod a b) = show a ++ "*" ++ show b
  show (Rec a) = "[" ++ show (head a) ++ "]"
  show (TypeError s) = s

instance Show (T) where
  show (Iso a b) = "(" ++ show a ++ "<-->" ++ show b ++ ")"
  show (Comp a b t) = "(" ++ show a ++ "<-->" ++ show b ++ ")" ++ "-->" ++ show t



-- Definição da Ortogonalidade de valores
(@@) :: V -> V -> Bool
(InjL v1) @@ (InjR v2) = True
(InjR v1) @@ (InjL v2) = True
(InjL v1) @@ (InjL v2) = v1 @@ v2
(InjR v1) @@ (InjR v2) = v1 @@ v2
(PairV v v1) @@ (PairV v' v2) = v1 @@ v2
-- (PairV v1 v) @@ (PairV v2 v') = v1 @@ v2 Por que esta definição existe?

--Function used to wrap evaluations of typing error raising functions
wrap :: Either TypeErrors a -> a
wrap (Left err) = error (show err)
wrap (Right val) = val


typeCheck :: Delta -> Psi -> Iso -> T -> T
typeCheck delta psi t a = checked a $ isoTypeCheck delta psi t a

checked :: T -> Either TypeErrors T -> T
checked a (Right b) = a
checked _ _ = error "should not execute ever"

-- TypeChecking definition for terms
mytermTypeCheck :: Delta -> Psi -> Term -> A -> Either TypeErrors A
mytermTypeCheck delta psi EmptyTerm a = Right One
mytermTypeCheck delta psi (XTerm x) a = Right (wrap $ matchTypes a (XTerm x) $ wrap $ myxType x $ xInContext x delta)
mytermTypeCheck delta psi (InjLt t) (Sum a b) = Right $ Sum (wrap $ matchTypes a t $ wrap $ mytermTypeCheck delta psi t a) b
mytermTypeCheck delta psi (InjRt t) (Sum a b) = Right $ Sum a (wrap $ matchTypes b t $ wrap $ mytermTypeCheck delta psi t b)
mytermTypeCheck delta psi (PairTerm t1 t2) (Prod a b) = Right $ Prod (wrap $ mytermTypeCheck delta psi t1 a) $ wrap $ mytermTypeCheck delta psi t2 b
            --On pairs: differentiate the contexts for each t. Is it necessary?
mytermTypeCheck delta psi (Omega f t) b = let isoInputType = checkIsoReturnType b $ wrap $ isoTypeCheck delta psi f (Iso One b)
                                          in if (wrap $ mytermTypeCheck delta psi t isoInputType) == isoInputType then Right b
                                            else Left $ OmegaError "Omega input of the wrong type" (Omega f t)
mytermTypeCheck delta psi (Let p t1 t2) c = let newDelta = wrap $ addToContext delta p $ wrap $ mytermTypeCheck delta psi t1 c
                                              in Right $ wrap $ mytermTypeCheck newDelta psi t2 c
mytermTypeCheck _ _ t a = Left $ CustomError "Cannot match term and type:" (show t ++ " : " ++ show a)
--Check if product and type provided are conductive to pairs. If so, extend the context
-- Otherwise raise a typing error.
addToContext :: Delta-> P -> A -> Either TypeErrors Delta
addToContext delta (PairP (Xprod x) (Xprod y)) (Prod a b) = Right $ delta ++ [(x,a),(y,b)]
addToContext delta (Xprod x) a = Right $ (x,a) : delta
addToContext _ (PairP p1 p2) _ = Left $ ProdError "Not a product Type" (PairP p1 p2)

--Retrieve the type of supplied value from context if it exists, otherwise return a TypeError
myxType :: String -> Maybe A -> Either TypeErrors A
myxType _ (Just v) = Right v -- Found the variable in the context, return its type
myxType x Nothing = Left $ VarError "Variable not in context: " x


xType :: Maybe A -> A
xType (Just v) = v -- Found the variable in the context, return its type
xType Nothing = TypeError "Variable not in context"

--Lookup variable x in the supplied context. If variable is found, returns Just A, otherwise returns Nothing
xInContext :: String -> Delta -> Maybe A
xInContext x delta = lookup x delta -- Lookup a -> [(a,b)] -> Maybe b
                                    -- Returns b if it finds a pair based on provided key a

--Retrieve type of iso named f from IsoContext psi
fType :: String -> Maybe T -> Either TypeErrors T --Instead of building typeclasses for the Context Lookup function instances, create a new one
fType f (Just t) = Right t
fType f Nothing = Left $ IsoError "Function not in context" f ""

--Lookup iso f in the supplied IsoContext. Returns Just T if iso is found, otherwise returns Nothing
fInContext :: String -> Psi -> Maybe T
fInContext f psi = lookup f psi

checkIsoReturnType ::  B -> T -> B
checkIsoReturnType b (Iso a b') = if b' == b then a
                                             else TypeError "Iso input type doesnt match Term"
checkIsoReturnType b _ = TypeError "Iso is not a function"

-- TypeChecking function for isomorphisms.
isoTypeCheck :: Delta -> Psi -> Iso -> T -> Either TypeErrors T
isoTypeCheck delta psi (IsoVar f) t = Right $ wrap $ fType f $ fInContext f psi
isoTypeCheck delta psi (Lambda f iso) t = let aB = breakIsoType t
                                            in Right $ wrap $ isoTypeCheck delta (addIsoNameToPsi psi f aB) iso $ snd aB
isoTypeCheck delta psi (App iso1 iso2) t = let iso1Type = fst $ breakIsoType $ wrap $ isoTypeCheck delta psi iso1 t
                                      in if (wrap $ isoTypeCheck delta psi iso2 iso1Type) == iso1Type then Right t
                                          else Left $ AppError "Cannot app isos" iso1 iso2
isoTypeCheck delta psi (Pattern list) (Iso a b) = let vList = map fst list
                                                      eList = map snd list
                                                      vTypes = wrap $ valueTypes delta vList a
                                                      eTypes = wrap $ extendedValueTypes delta eList b
                                                      odA = wrap $ orthogonalDecomposition delta a [] vList
                                                      odB = wrap $ extOrthogonalDecomposition delta b [] eList
                                                  in Right (Iso a b) -- Make it right!
isoTypeCheck _ _ iso t = Left $ IsoError "Could not match supplied iso" (show iso) (show t)

--Checks supplied values' types, returning an error if one doesn't match the expected type,
valueTypes :: Delta -> [V] -> A -> Either TypeErrors A
valueTypes delta [] a = Right a
valueTypes delta (v:vals) a = if (valueTypeCheck delta v a) == a then valueTypes delta vals a
                              else Left $ ValueError "Value V doesnt match supplied type" v a

--Implementar a função para verificar os tipos dos ExtendedValues!!
extendedValueTypes :: Delta -> [E] -> B -> Either TypeErrors B
extendedValueTypes delta eList b = let bottomVals = map bottomValue eList in valueTypes delta bottomVals b

addIsoNameToPsi :: Psi -> String -> (T,T) -> Psi
addIsoNameToPsi psi f types = (f,fst types) : psi

breakIsoType :: T -> (T,T)
breakIsoType (Comp a b t) = (Iso a b , t)
breakIsoType t = error $ "Iso is not a computation" ++ show t

matchTypes :: A -> Term -> B -> Either TypeErrors B
--Receives two types, returning the type if they match, a TypeError otherwise. Term is included so the error message is better defined
matchTypes a t b
        | a == b = Right a
        | otherwise = Left $ SumError "SumTypes differ on term: " t


--Creates the set defining a OrthogonalDecomposition (OD) of value A.
orthogonalDecomposition :: Delta -> A -> OD -> [V] -> Either TypeErrors OD
orthogonalDecomposition delta One od _  = Right $ [EmptyV]
orthogonalDecomposition delta a od [Xval x]  = Right $ [Xval x]
orthogonalDecomposition delta (Sum a b) od patterns  = let  s = fst $ getInjValues patterns
                                                            t =  snd $ getInjValues patterns
                                                            odS = wrap $ orthogonalDecomposition delta a od s
                                                            odT = wrap $ orthogonalDecomposition delta b od t
                                                            in Right $ odS ++ odT --Se as decomposições são válidas, a união de ambas é uma OD.
              --Preciso implementar o conceito de free-variables neste caso!!
orthogonalDecomposition delta (Prod a b) od patterns = let s = breakPairs patterns 1 --Get first elem of pairs
                                                           t = breakPairs patterns 2 --Get second elem of pairs
                                                           odS = wrap $ orthogonalDecomposition delta a od s
                                                           odT = wrap $ orthogonalDecomposition delta b od t
                                                           freeValsV2 = freeValueVariables t
                                                           freeValsV1 = freeValueVariables s
                                                           -- Se existe intersecçao de FreeVariables, retorna um conjunto Vazio, não é uma OD.
                                                           in if freeValIntersects freeValsV1 freeValsV2
                                                                then Left $ OrthogonalDecomp "Patterns dont make an orthogonal Decomposition!" patterns
                                                                else Right patterns
orthogonalDecomposition delta a od [] = Left $ OrthogonalDecomp "Cannot generate Orthogonal Decomposition:!" []
--Definition of orthogonalDecomposition for extendedValues: OD(ExtVal) is true whenever OD(Val(ExtVal)) is true.
extOrthogonalDecomposition :: Delta -> B -> OD -> [E] ->Either TypeErrors OD
extOrthogonalDecomposition delta b od eList = orthogonalDecomposition delta b od $ map bottomValue eList

--Returns a pair of lists, the first being all InjL values and the second all InjR values.
--Will return an empty list as one of the members if there is no value of either of the indicated Types
getInjValues :: [V] -> ([V],[V])
getInjValues [] = ([],[])
getInjValues injectives = (leftValues injectives , rightValues injectives)
--Returns a set of all InjL values.
leftValues :: [V] -> [V]
leftValues [] = []
leftValues ((InjL v):injectives) = v : leftValues injectives
leftValues ((InjR v):injectives) = [] ++ leftValues injectives
--Returns a set of all InjR values.
rightValues :: [V] -> [V]
rightValues [] = []
rightValues ((InjR v):injectives) = v : rightValues injectives
rightValues ((InjL v):injectives) = [] ++ rightValues injectives
--Breaks pairs into one of their value components, based on the supplied Int
-- For 1, returns all of the fst members of the pairs. For 2, all of the snd members of the pairs.
breakPairs :: [V] -> Int  -> [V]
breakPairs [] _ = []
breakPairs pairs 1 = map getFstFromPair pairs
breakPairs pairs 2 = map getSndFromPair pairs

getFstFromPair :: V -> V
getFstFromPair (PairV p1 p2) = p1

getSndFromPair :: V -> V
getSndFromPair (PairV p1 p2) = p2

--Returns the bottom value from an Extended Value. (Val(e))
bottomValue :: E -> V
bottomValue (Val v) = v
bottomValue (LetE p1 iso p2 e) = bottomValue e

freeValueVariables :: [V] -> [String]
freeValueVariables [] = []
freeValueVariables ((Xval x):values) = x : freeValueVariables values
freeValueVariables ((InjL v):values) = freeValueVariables [v] ++ freeValueVariables values
freeValueVariables ((InjR v):values) = freeValueVariables [v] ++ freeValueVariables values
freeValueVariables ((PairV v1 v2):values) = freeValueVariables [v1] ++ freeValueVariables [v2] ++ freeValueVariables values

--Tests the intersection of freeVariable lists, returning True for intersection, False for no intersection
freeValIntersects :: [String] -> [String] -> Bool
freeValIntersects fv1 fv2 = not . null $ fv1 `intersect` fv2

errorOrType :: Either TypeErrors A -> V -> [V]
errorOrType (Right a) v = [v]
errorOrType (Left e) v = []

--(.) :: (b -> c) -> (a -> b) -> a -> c
valueTypeCheck ::  Delta -> V -> A  -> A
valueTypeCheck delta EmptyV One = One
valueTypeCheck delta (Xval x) a =  xType $ xInContext x delta
valueTypeCheck delta (InjL v) (Sum a b) = valueTypeCheck delta v b
valueTypeCheck delta (InjR v) (Sum a b) = valueTypeCheck delta v a
valueTypeCheck delta (PairV v v2) (Prod a b) = Prod (valueTypeCheck delta v a) $ valueTypeCheck delta v2 b
-- Sums [(Alpha,V)]

-- termTypeCheck :: Delta -> Psi -> Term -> A -> A
-- termTypeCheck delta psi EmptyTerm a = One
-- termTypeCheck delta psi (XTerm x) a = matchTypes a $ xType $ xInContext x delta
-- termTypeCheck delta psi (InjLt t) (Sum a b) = Sum (matchTypes a $ termTypeCheck delta psi t a) b
-- termTypeCheck delta psi (InjRt t) (Sum a b) = Sum a (matchTypes b $ termTypeCheck delta psi t b)
-- termTypeCheck delta psi (PairTerm t1 t2) (Prod a b) = Prod (termTypeCheck delta psi t1 a) $ termTypeCheck delta psi t2 b
--             --On pairs: differentiate the contexts for each t. Is it necessary?
-- termTypeCheck delta psi (Omega f t) b = termTypeCheck delta psi t $ checkIsoReturnType b $ isoTypeCheck psi f (Iso One b)
-- termTypeCheck delta psi (Let p t1 t2) c = let newDelta = fillPairTypes delta p $ termTypeCheck delta psi t1 c
--                                             in termTypeCheck newDelta psi t2 c
--
--
-- fillPairTypes :: Delta-> P -> A -> Delta
-- fillPairTypes delta (PairP (Xprod x) (Xprod y)) (Prod a b) = delta ++ [(x,a),(y,b)]
-- fillPairTypes _ _ _ = error "Not expected operation"



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
