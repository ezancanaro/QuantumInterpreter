module Quantum where
import Data.Complex
import Data.List
import Debug.Trace

--Debugging flag-
doDebug = False
--Making debug statements easier to use
debug a b = if doDebug then trace a b else b
--Remember to remove debugging statements after checks

data A =  One -- 1
        | Sum A B -- a + b
        | Prod A B -- a * b
        | Rec A -- [a] == 1 + (a * [a]) --Sum One (Prod A (Rec A))
                -- listX == ()|<x,listX> --[] or (x:listX)
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
        deriving(Eq)
data P =  EmptyP
        | Xprod String --Equivale ao par <(),x>
        | PairP P P
        deriving(Eq)
data E =  Val V
        | LetE P Iso P E
        deriving(Eq,Show)

data Iso = Lambda String Iso
        | IsoVar String
        | App Iso Iso
        | Pattern [(V,E)]
        deriving(Eq)

data Term = EmptyTerm
        | XTerm String
        | InjLt Term
        | InjRt Term
        | PairTerm Term Term
        | Omega Iso Term
        | Let P Term Term
        deriving(Eq)

data TypeErrors = VarError String String
        | SumError String String
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

--Making it easier to see the outputs
instance Show (A) where
  show (One) = "1"
  show (Sum a b) = show a ++ "+" ++ show b
  show (Prod a b) = show a ++ "*" ++ show b
  show (Rec (Sum one (Prod a recA))) = "[" ++ show a ++ "]"
  show (TypeError s) = s

instance Show (T) where
  show (Iso a b) = "(" ++ show a ++ "<-->" ++ show b ++ ")"
  show (Comp a b t) = "(" ++ show a ++ "<-->" ++ show b ++ ")" ++ "-->" ++ show t

instance Show (V) where
  show (EmptyV) = "()"
  show (Xval s) = s
  show (InjL v) = "InjL" ++ show v
  show (InjR v) = "InjR" ++ show v
  show (PairV v1 v2) = "<" ++ show v1 ++ "," ++ show v2 ++ ">"

instance Show (P) where
  show (EmptyP) = "()"
  show (Xprod s) = s
  show (PairP p1 p2) = "<" ++ show p1 ++ "," ++ show p2 ++ ">"

instance Show (Term) where
  show (EmptyTerm) = "()"
  show (XTerm s) = s
  show (InjLt t) = "InjL" ++ show t
  show (InjRt t) = "InjR" ++ show t
  show (PairTerm t1 t2) = "<" ++ show t1 ++ "," ++ show t2 ++ ">"
  show (Omega iso t1) = show iso ++ " " ++ show t1
  show (Let p t1 t2) = "let " ++ show p ++ "=" ++ show t1 ++ " in " ++ show t2

instance Show (Iso) where
  show (Lambda s iso) = "Lam" ++ s ++ "." ++ show iso
  show (IsoVar s) = s
  show (App iso1 iso2) = show iso1 ++ " " ++ show iso2
  show (Pattern list) = showPatterns list

showPatterns :: [(V,E)] -> String
showPatterns [] = []
showPatterns (p1:patterns) = show (fst p1) ++ "<-->" ++ show (snd p1) ++ "\n" ++ showPatterns patterns

-----------------------------------------------------------------------------------------------------------------
--              TypeChecker                     --
-- Value orthogonality
(@@) :: V -> V -> Bool
(InjL v1) @@ (InjR v2) = True
(InjR v1) @@ (InjL v2) = True
(InjL v1) @@ (InjL v2) = v1 @@ v2
(InjR v1) @@ (InjR v2) = v1 @@ v2
(PairV v v1) @@ (PairV v' v2) = v1 @@ v2
-- (PairV v1 v) @@ (PairV v2 v') = v1 @@ v2 ??

--Function used to wrap evaluations of functions tha may raise a typing error.
--We use to avoid creating multiple conditionals on the function definitions. Needs a better name!!!
wrap :: Either TypeErrors a -> a
wrap (Left err) = error (show err)
wrap (Right val) = val

--Entry point for the tests from main.
typeCheck :: Delta -> Psi -> Iso -> T -> T
typeCheck delta psi iso t = wrap $ isoTypeCheck delta psi iso t


-- TypeChecking definition for terms
mytermTypeCheck :: Delta -> Psi -> Term -> A -> Either TypeErrors A
mytermTypeCheck delta psi EmptyTerm a = Right One
--IF variable x is in context with type matching a, return the type
mytermTypeCheck delta psi (XTerm x) a = Right (wrap $ matchTypes a (XTerm x) $ wrap $ myxType x $ xInContext x delta)
--Typecheck term t and match resulting type with a. If it matches return a+b.
mytermTypeCheck delta psi (InjLt t) (Sum a b) = Right $ Sum (wrap $ matchTypes a t $ wrap $ mytermTypeCheck delta psi t a) b
--Typecheck term t and match resulting type with b. If it matches return a+b.
mytermTypeCheck delta psi (InjRt t) (Sum a b) = Right $ Sum a (wrap $ matchTypes b t $ wrap $ mytermTypeCheck delta psi t b)
--Typecheck t1 with a, t2 with b. If they succeed, return a * b --On pairs: differentiating the contexts for each t is necessary?
mytermTypeCheck delta psi (PairTerm t1 t2) (Prod a b) = Right $ Prod (wrap $ mytermTypeCheck delta psi t1 a) $ wrap $ mytermTypeCheck delta psi t2 b
--Typecheck the iso f, match t with the first part of resulting type ("input"). If they match, return type b
mytermTypeCheck delta psi (Omega f t) b = let isoInputType = checkIsoReturnType b $ wrap $ isoTypeCheck delta psi f (Iso One b)
                                          in if (wrap $ mytermTypeCheck delta psi t isoInputType) == isoInputType then Right b
                                            else Left $ OmegaError "Omega input of the wrong type" (Omega f t)
--Typecheck t1 and use resulting type to add variables from p to the context. Using the new context, typecheck t2 with type c.
mytermTypeCheck delta psi (Let p t1 t2) c = let newDelta = wrap $ addToContext delta p $ wrap $ mytermTypeCheck delta psi t1 c
                                              in Right $ wrap $ mytermTypeCheck newDelta psi t2 c
--Whenever typeChecking fails, we return a Left value showing the matching error. Could make it more descriptive?
mytermTypeCheck _ _ t a = Left $ CustomError "Cannot match term and type:" (show t ++ " : " ++ show a)

--TypeChecking for values, same behavior as termTypeCheck
valueTypeCheck ::  Delta -> V -> A  ->Either TypeErrors A
valueTypeCheck delta EmptyV One = Right One
valueTypeCheck delta (Xval x) a =  Right (wrap $ matchTypes a (XTerm x) $ wrap $ myxType x $ xInContext x delta)
valueTypeCheck delta (InjL v) (Sum a b) = Right $ Sum (wrap $ matchTypes a v $ wrap $ valueTypeCheck delta v a) b
valueTypeCheck delta (InjR v) (Sum a b) = Right $ Sum a (wrap $ matchTypes a v $ wrap $ valueTypeCheck delta v b)
valueTypeCheck delta (PairV v v2) (Prod a b) = Right $ Prod (wrap $ valueTypeCheck delta v a) $ wrap $ valueTypeCheck delta v2 b
valueTypeCheck _ v a = Left $ CustomError "Value matching failed:" (show v ++ ":" ++ show a)
--TypeChecking for special products cases. Not 100% ...
productsTypecheck :: Delta ->  P -> A -> Either TypeErrors A
productsTypecheck delta (Xprod x) a = valueTypeCheck delta (Xval x) a
productsTypecheck delta (PairP p1 p2) (Prod a b) = Right $ Prod (wrap $ productsTypecheck delta p1 a) $ wrap $ productsTypecheck delta p2 b
productsTypecheck delta p _ = Left $ CustomError "Product typechecking error" (show p)
--TypeChecking for extendedValues. Needed?
extendedValueTypeCheck :: Delta -> Psi -> E -> A -> Either TypeErrors A
extendedValueTypeCheck delta psi (Val v) a = valueTypeCheck delta v a
extendedValueTypeCheck delta psi (LetE p1 iso p2 e) a = let isoType = wrap $ getIsoTypes $ wrap $ isoTypeFromPsi $ isoLookup iso psi
                                                            p2Type = wrap $ productsTypecheck delta p2 $ fst isoType
                                                            bottomVal = bottomValue e
                                                          in if(fst isoType == p2Type)
                                                              then valueTypeCheck (addProductToContext delta p1 $ snd isoType) bottomVal a
                                                             else Left $ ProdError "Product not input of Iso" p2

-- TypeChecking function for isomorphisms.
isoTypeCheck :: Delta -> Psi -> Iso -> T -> Either TypeErrors T
--Check that iso variable is in the context with matching type t.
isoTypeCheck delta psi (IsoVar f) t = Right $ wrap $ matchIsoTypes t (IsoVar f) $ wrap $ fType f $ fInContext f psi
--Add isoVariable f to context with type (a<->b) and typeCheck iso with resulting context and type t
isoTypeCheck delta psi (Lambda f iso) (Comp a b t) =  Right (Comp a b $ wrap $ isoTypeCheck delta (addIsoNameToPsi psi f (Iso a b)) iso t)
--I'm pretty sure this is wrong. REDO it.
isoTypeCheck delta psi (App iso1 iso2) t = let iso1Type = fst $ breakIsoType $ wrap $ isoTypeCheck delta psi iso1 t
                                            in if (wrap $ isoTypeCheck delta psi iso2 iso1Type) == iso1Type then Right t
                                          else Left $ AppError "Cannot app isos" iso1 iso2
--Get lists of values and extendedValues and typeCheck them. If they are not all of the same value, wrap will catch it.
--Create the orthogonal decomposition sets for both lists, if the creation fails we get a Left value caught by wrap.
--Test that the values match Type a and extendedValues match type b. If so, typechecking succeeds, else we return an error.
isoTypeCheck delta psi (Pattern list) (Iso a b) = let vList = map fst list
                                                      eList = map snd list
                                                      vTypes = wrap $ valueTypes delta vList a
                                                      eTypes = debug("Values:" ++ show vTypes)
                                                                wrap $ extendedValueTypes delta psi eList b
                                                      odA = wrap $ orthogonalDecomposition delta a [] vList
                                                      odB = wrap $ extOrthogonalDecomposition delta b [] eList
                                                  in if (eTypes == b && vTypes == a) then Right $ Iso a b
                                                      else Left $ IsoError "Iso patterns dont match type:" (show (Pattern list)) (show (Iso a b))--Need to garantee correct checking of vals and extVals still
--If typeChecking fails return a Left value with an error.
isoTypeCheck _ _ iso t = Left $ IsoError "Could not match supplied iso" (show iso) (show t)

addProductToContext :: Delta -> P -> A -> Delta
addProductToContext delta (EmptyP) a = delta
addProductToContext delta (Xprod x) a = (x,a):delta
addProductToContext delta (PairP p1 p2) (Prod a b) = addProductToContext delta p1 a ++ addProductToContext delta p2 b

getIsoTypes :: T -> Either TypeErrors (A,B)
getIsoTypes (Iso a b) = Right (a,b)
getIsoTypes iso = Left $ IsoError "Not an isoType" (show iso) ""

isoTypeFromPsi :: Maybe T -> Either TypeErrors T
isoTypeFromPsi (Just t) = Right t
isoTypeFromPsi Nothing = Left $ IsoError "Iso not found in context: " "" ""

isoLookup :: Iso -> Psi -> Maybe T
isoLookup (IsoVar s) psi = lookup s psi
isoLookup (Lambda s iso) psi = lookup s psi
isoLookup _ _= Nothing

--Check if product and type provided are conductive to pairs. If so, extend the context
-- Otherwise return a typing error.
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

--Returns iso input type if Iso's output type matches supplied b
checkIsoReturnType ::  B -> T -> B
checkIsoReturnType b (Iso a b') = if b' == b then a
                                             else TypeError "Iso input type doesnt match Term"
checkIsoReturnType b _ = TypeError "Iso is not a function"



--Checks supplied values' types, returning an error if one doesn't match the expected type,
valueTypes :: Delta -> [V] -> A -> Either TypeErrors A
valueTypes delta [] a = Right a
valueTypes delta (v:vals) a = if (wrap $ valueTypeCheck delta v a) == a then debug("Value checked:" ++ show a)
                                                                              valueTypes delta vals a
                              else debug("Values didnot match: " ++ show a)
                                    Left $ ValueError "Value V doesnt match supplied type" v a

--Implementar a função para verificar os tipos dos ExtendedValues!!
extendedValueTypes :: Delta -> Psi -> [E] -> B -> Either TypeErrors B
extendedValueTypes delta psi ((LetE p1 iso p2 e):listE) b = Right b
extendedValueTypes delta psi eList b = let bottomVals = map bottomValue eList
                                        in valueTypes delta bottomVals b

addIsoNameToPsi :: Psi -> String -> T -> Psi
addIsoNameToPsi psi f t = (f,t) : psi

breakIsoType :: T -> (T,T)
breakIsoType (Comp a b t) = (Iso a b , t)
breakIsoType t = error $ "Iso is not a computation" ++ show t

--Receives two types, returning the type if they match, a TypeError otherwise.
-- Argument type a is used to accept both Values and Terms, both of which have defined instances of Show.
matchTypes :: Show a => A -> a -> B -> Either TypeErrors B
matchTypes a t b
        | a == b = Right a
        | otherwise = Left $ VarError "Variable type doesnt match supplied A " (show t ++ ":" ++ show b ++ "not " ++ show a)

--Match types of Iso, supplied to typechecker and found in context.
matchIsoTypes :: T -> Iso -> T -> Either TypeErrors T
matchIsoTypes a iso b
        | a == b = Right a
        | otherwise = Left $ VarError "IsoVariable type doesnt match supplied T " (show iso ++ ":" ++ show b ++ "not " ++ show a)

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
