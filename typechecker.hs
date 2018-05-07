module Typechecker where
import AbstractData
import Utils
--Pure version of the Typechecker ..
import Data.Number.CReal
import Data.Complex
import Data.List
import Data.Matrix

-- import Linear.Matrix -- Needs installing via Cabal


-----------------------------------------------------------------------------------------------------------------
--              TypeChecker       -- Could probably be implemented with the use of a Reader monad
                                  -- for carrying the contexts around. Should look into it.
-- Value orthogonality
(@@) :: V -> V -> Bool
(InjL v1) @@ (InjR v2) = True
(InjR v1) @@ (InjL v2) = True
(InjL v1) @@ (InjL v2) = v1 @@ v2
(InjR v1) @@ (InjR v2) = v1 @@ v2
(PairV v v1) @@ (PairV v' v2) = v1 @@ v2
-- (PairV v1 v) @@ (PairV v2 v') = v1 @@ v2 ??


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
--Typing clause for Recursive list Types empty lists.
mytermTypeCheck delta psi (InjLt EmptyTerm) (Rec a) = Right $ Rec a --Valid????
--Typecheck term t and match resulting type with b. If it matches return a+b.
mytermTypeCheck delta psi (InjRt t) (Sum a b) = Right $ Sum a (wrap $ matchTypes b t $ wrap $ mytermTypeCheck delta psi t b)
--TypeChecking clause for supporting Recursive list Types constructors (x:list)
mytermTypeCheck delta psi (InjRt (PairTerm t1 t2)) (Rec a) = let a' = wrap $ mytermTypeCheck delta psi t1 a
                                                                 recA = wrap $ mytermTypeCheck delta psi t2 (Rec a)
                                                              in if (a' == a) then Right $ Rec a
                                                                 else Left $ CustomError "Constructor pair is wrong:" (show t1 ++ ":" ++ show t2 ++ show a)
--Typecheck t1 with a, t2 with b. If they succeed, return a * b --On pairs: differentiating the contexts for each t is necessary?
mytermTypeCheck delta psi (PairTerm t1 t2) (Prod a b) = Right $ Prod (wrap $ mytermTypeCheck delta psi t1 a) $ wrap $ mytermTypeCheck delta psi t2 b
--Typecheck the iso f, match t with the first part of resulting type ("input"). If they match, return type b
mytermTypeCheck delta psi (Omega f t) b = let isoInputType = wrap $ checkIsoReturnType b $ wrap $ isoTypeCheck delta psi f (Iso (TypeVar 'a') b)
                                          in if (wrap $ mytermTypeCheck delta psi t isoInputType) == isoInputType then Right b
                                            else Left $ OmegaError "Omega input of the wrong type" (Omega f t)
--Typecheck t1 and use resulting type to add variables from p to the context. Using the new context, typecheck t2 with type c.
mytermTypeCheck delta psi (Let p t1 t2) c = let newDelta = wrap $ addToContext delta p $ wrap $ mytermTypeCheck delta psi t1 c
                                              in Right $ wrap $ mytermTypeCheck newDelta psi t2 c
mytermTypeCheck delta psi (CombTerms t1 t2) c = let t1Type = mytermTypeCheck delta psi t1 c
                                                    t2Type = mytermTypeCheck delta psi t2 c --
                                                in if t1Type == t2Type then Right c -- Only passes if terms are of the same type and same FreeVariables
                                                                                    -- Need to Implement test for FreeVariables of both terms.
                                                   else Left $ CustomError "Term combination failed, terms not of same type:" (show t1 ++ ":" ++ show t1Type ++ show t2 ++ ":" ++ show t2Type)
mytermTypeCheck delta psi (AlphaTerm a t) c = mytermTypeCheck delta psi t c -- Typechecking doesn't care about the alpha.
--Whenever typeChecking fails, return a Left value showing the matching error. Could make it more descriptive?
mytermTypeCheck _ _ t a = Left $ CustomError "Cannot match term and type:" (show t ++ " : " ++ show a)

--TypeChecking for values, same behavior as termTypeCheck
valueTypeCheck ::  Delta -> V -> A  ->Either TypeErrors A
valueTypeCheck delta EmptyV One = Right One
valueTypeCheck delta (Xval x) a =  Right (wrap $ matchTypes a (XTerm x) $ wrap $ myxType x $ xInContext x delta)
valueTypeCheck delta (InjL v) (Sum a b) = Right $ Sum (wrap $ matchTypes a v $ wrap $ valueTypeCheck delta v a) b
valueTypeCheck delta (InjL (EmptyV)) (Rec a) = Right $ Rec a -- ??????
valueTypeCheck delta (InjR v) (Sum a b) = Right $ Sum a (wrap $ matchTypes a v $ wrap $ valueTypeCheck delta v b)
valueTypeCheck delta (InjR (PairV v1 v2)) (Rec a) = let a' = wrap $ valueTypeCheck delta v1 a -- ????
                                                        recA = debug("Checking: " ++ (show v2))
                                                                wrap $ valueTypeCheck delta v2 (Rec a)
                                                    in case recA of
                                                        Rec r -> if (a' == a) then Right $ Rec a
                                                                   else Left $ CustomError "Constructor pair is wrong:" (show v1 ++ ":" ++ show v2 ++ show a)
                                                        otherwise -> Left $ CustomError "Right element of pair not a list" (show (PairV v1 v2))
valueTypeCheck delta (PairV v v2) (Prod a b) = Right $ Prod (wrap $ valueTypeCheck delta v a) $ wrap $ valueTypeCheck delta v2 b
valueTypeCheck _ v a = Left $ CustomError "Value matching failed:" (show v ++ ":" ++ show a)
--TypeChecking for special products cases. Not 100% ...
productsTypecheck :: Delta ->  P -> A -> Either TypeErrors A
productsTypecheck delta (Xprod x) a = valueTypeCheck delta (Xval x) a
productsTypecheck delta (PairP p1 p2) (Prod a b) = Right $ Prod (wrap $ productsTypecheck delta p1 a) $ wrap $ productsTypecheck delta p2 b
productsTypecheck delta p _ = Left $ CustomError "Product typechecking error" (show p)
--TypeChecking for extendedValues. ?
extendedValueTypeCheck :: Delta -> Psi -> E -> A -> Either TypeErrors A
extendedValueTypeCheck delta psi (Val v) a = valueTypeCheck delta v a
extendedValueTypeCheck delta psi (LetE p1 iso p2 e) a = let isoType = wrap $ getIsoTypes $ wrap $ isoTypeFromPsi $ isoLookup iso psi
                                                            p2Type = wrap $ productsTypecheck delta p2 $ fst isoType
                                                            --bottomVal = bottomValue e
                                                          in if(fst isoType == p2Type)
                                                              then debug("LetExtVal: adding p1 to context:" ++ (show p1) ++ ": " ++ (show (snd isoType)))
                                                                    extendedValueTypeCheck (addProductToContext delta p1 $ snd isoType) psi e a
                                                             else Left $ ProdError "Product not input of Iso" p2
extendedValueTypeCheck delta psi (Combination e1 e2) a = let e1Type = wrap $ extendedValueTypeCheck delta psi e1 a
                                                             e2Type = wrap $ extendedValueTypeCheck delta psi e2 a
                                                             in if(e1Type == e2Type && e1Type == a) then Right a
                                                                else Left $ CustomError "Combination of extendedValues of differing types" ("e1:" ++ show e1Type ++ " " ++ "e1:" ++ show e2Type)
extendedValueTypeCheck delta psi (AlphaVal alpha e) a = extendedValueTypeCheck delta psi e a
-- checkLinearCombinationExtVals :: Delta -> Psi -> E -> A -> Either TypeErrors A
-- checkLinearCombinationExtVals _ _ (Val []) a = Right a
-- checkLinearCombinationExtVals delta psi (Val alphaV:vals) a = if valueTypeCheck delta (snd alphaV) a == (Right a) then
--                                                                 checkLinearCombinationExtVals delta psi (Val vals) a
--                                                               else Left $ CustomError "Linear Combination of ExtVals failed typechecking" ""

-- TypeChecking function for isomorphisms.
isoTypeCheck :: Delta -> Psi -> Iso -> T -> Either TypeErrors T
--Check that iso variable is in the context with matching type t.
isoTypeCheck delta psi (IsoVar f) (Iso (TypeVar a) b) = Right $ wrap $ fType f $ fInContext f psi -- Case where variable is an already typed function. Eg: Iso application f (g term), f needs to be an already declared iso.
isoTypeCheck delta psi (IsoVar f) t = Right $ wrap $ matchIsoTypes t (IsoVar f) $ wrap $ fType f $ fInContext f psi
--Add isoVariable f to context with type (a<->b) and typeCheck iso with resulting context and type t
isoTypeCheck delta psi (Lambda f iso) (Comp a b t) =  Right (Comp a b $ wrap $ isoTypeCheck delta (addIsoNameToPsi psi f (Iso a b)) iso t)
--Iso application. Since isos don't carry type annotations, typecheck iso1 with a dummy type consisting of TypeVars in order to get back the real type
isoTypeCheck delta psi (App iso1 iso2) t = let iso1Type = breakIsoType $ wrap $ isoTypeCheck delta psi iso1 (Comp (TypeVar 'a') (TypeVar 'b') t)
                                               iso1Left = fst iso1Type
                                               iso1Right = snd iso1Type
                                               --Check that Left-hand size of Type is the same as iso2's type AND that Right-hand side equals application type
                                            in if (wrap $ isoTypeCheck delta psi iso2 iso1Left) == iso1Left && iso1Right == t then Right t
                                          else Left $ AppError "Cannot app isos" iso1 iso2
--Get lists of values and extendedValues and typeCheck them. If they are not all of the same value, wrap will catch it.
--Create the orthogonal decomposition sets for both lists, if the creation fails we get a Left value caught by wrap.
--Test that the values match Type a and extendedValues match type b. If so, typechecking succeeds, else we return an error.
isoTypeCheck delta psi (Clauses list) (Iso a b) = let vList = map fst list
                                                      eList = map snd list
                                                      vTypes = wrap $ valueTypes delta vList a
                                                      eTypes = debug("Values:" ++ show vTypes)
                                                                wrap $ extendedValueTypes delta psi eList b
                                                      odA = orthogonalDecomposition delta a [] vList
                                                      odB = extOrthogonalDecomposition delta b [] eList
                                                      unitary = testUnit eList
                                                  in if (checkODs odA odB a b) && (eTypes == b) && (vTypes == a) then
                                                        if(unitary) then Right $ Iso a b --Separate the tests to specify the error.
                                                        else Left $ IsoError "Not a unitary Matrix!" "\n" (show (Clauses list))
                                                     else Left $ IsoError "Iso Clausess dont match type:" (show (Clauses list)) (show (Iso a b))--Need to garantee correct checking of vals and extVals still
--Typecheck Fixpoints here.
isoTypeCheck delta psi (Fixpoint f iso) t = if fixpointTerminates psi (Fixpoint f iso) -- Not implemented.
                                              then Right $ wrap $ isoTypeCheck delta (addIsoNameToPsi psi f t) iso t
                                            else Left $ FixpointError "Fixpoint does not terminate: " (show (Fixpoint f iso))
                                  --If Fixpoint terminates in a finite context, then:
                                --Right (Comp a b $ wrap $ isoTypeCheck delta (addIsoNameToPsi psi f (Iso a b)) iso (Comp a b t))
--If typeChecking fails return a Left value with an error.
isoTypeCheck _ _ iso t = Left $ IsoError "Could not match supplied iso" (show iso) (show t)


checkODs ::  Either TypeErrors OD -> Either TypeErrors OD -> A -> B -> Bool
checkODs (Right v) (Right e) _ _ = True
checkODs (Left v) (Right e) t1 _ = error $ "Values are not an OrthogonalDecomp of " ++ show t1 ++ ":\n\t" ++ show v
checkODs (Right v) (Left e) t1 t2 = error $ "Expressions are not an OrthogonalDecomp of " ++ show t2 ++ ":\n\t" ++ show e
checkODs (Left v) (Left e) t1 t2 = error $ "Values nor Expressions are not an OrthogonalDecomp of " ++ show t1 ++ ","++ show t2++":\n\t" ++ show v ++ "\n\t" ++ show e

--Check fixpoint termination...
fixpointTerminates :: Psi -> Iso -> Bool
fixpointTerminates _ _ = True

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


xType :: Maybe A -> Either TypeErrors A
xType (Just v) = Right v -- Found the variable in the context, return its type
xType Nothing = Left $ VarError "Variable not in context" ""

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
checkIsoReturnType ::  B -> T -> Either TypeErrors B
checkIsoReturnType b (Iso a b') = if b' == b then Right a
                                             else Left $ IsoError "Iso input type doesnt match Term" (show $ Iso a b') (show b)
checkIsoReturnType b t = Left $ CustomError "Iso is not a function has type: " (show t)



--Checks supplied values' types, returning an error if one doesn't match the expected type,
valueTypes :: Delta -> [V] -> A -> Either TypeErrors A
valueTypes delta [] a = Right a
valueTypes delta (v:vals) a = if (wrap $ valueTypeCheck delta v a) == a then debug("Value checked:" ++ show a)
                                                                              valueTypes delta vals a
                              else debug("Values didnot match: " ++ show a)
                                    Left $ ValueError "Value V doesnt match supplied type" v a

--Implementar a função para verificar os tipos dos ExtendedValues!!
extendedValueTypes :: Delta -> Psi -> [E] -> B -> Either TypeErrors B
extendedValueTypes delta psi [] b = Right b
extendedValueTypes delta psi (e1:listE) b = -- debug ("extValTypes..")
                                              if (b == wrap (extendedValueTypeCheck delta psi e1 b) )
                                                then extendedValueTypes delta psi listE b
                                              else Left $ CustomError "Extended Value not matching Type" (show e1 ++ " : "++ show b)


addIsoNameToPsi :: Psi -> String -> T -> Psi
addIsoNameToPsi psi f t = (f,t) : psi

breakIsoType :: T -> (T,T)
breakIsoType (Comp a b t) = (Iso a b , t)
breakIsoType t = error $ "Iso is not a computation" ++ show t

--Receives two types, returning the type if they match, a TypeError otherwise.
-- Argument type a is used to accept both Values and Terms, both of which have defined instances of Show.
matchTypes :: Show a => A -> a -> B -> Either TypeErrors B
matchTypes supplied t found
        | supplied == found = Right supplied
        | otherwise = Left $ VarError "Variable type doesnt match supplied A " (show t ++ ":" ++ show found ++ "not " ++ show supplied)

--Match types of Iso, supplied to typechecker and found in context.
matchIsoTypes :: T -> Iso -> T -> Either TypeErrors T
matchIsoType (Iso (TypeVar a) b) iso (Iso a' b') --Used when I don't know iso "input" type beforehand, only care about it's ouput.
        | b == b' = Right $ Iso a' b'
        | otherwise = Left $ VarError "IsoVarible output type doesnt match supplied A" (show iso ++ ":" ++ show b' ++ "not" ++ show b)
matchIsoTypes supplied iso found
        | supplied == found = Right supplied
        | otherwise = Left $ VarError "IsoVariable type doesnt match supplied T " (show iso ++ ":" ++ show found ++ "not " ++ show supplied)

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
                                                                then Left $ OrthogonalDecomp "Clausess dont make an orthogonal Decomposition!" patterns
                                                                else Right patterns
orthogonalDecomposition delta (Rec a) od (InjL EmptyV : pat) = Right $ [InjL EmptyV] ++ (wrap $ orthogonalDecomposition delta (Rec a) od pat)
orthogonalDecomposition delta (Rec a) od (InjR (PairV v vtail) : pat) = let vals = decomposeList (InjR (PairV v vtail))
                                                                            od1 = wrap $ orthogonalDecomposition delta a od vals
                                                                            od2 = wrap $ orthogonalDecomposition delta (Rec a) od pat
                                                                        in Right $ od1 ++ od2
orthogonalDecomposition delta a od [] = Left $ OrthogonalDecomp "Cannot generate Orthogonal Decomposition:!" []
orthogonalDecomposition delta a od l = error $ "D" ++ show delta ++ show a ++ show l

decomposeList ::  V -> [V]
decomposeList (InjL EmptyV) = []
decomposeList (InjR (PairV v1 vtail)) = v1 : decomposeList vtail


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

freeValueVariables :: [V] -> [String]
freeValueVariables [] = []
freeValueVariables ((EmptyV):values) = freeValueVariables values
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


testUnit::[E]->Bool
testUnit = isUnitary . getLinearTerms

-- Bypass the need to build a matrix for isos defined in the classical setting. Could probably do with a smarter version of this.
oneZeroes :: [Alpha] -> Bool
oneZeroes [] = True
oneZeroes (h:t)
  | h /= 0 && h/= 1 = False
  | otherwise = oneZeroes t

oZ :: [[Alpha]] -> Bool
oZ [] = True
oZ (h:t)
  | not (oneZeroes h) = False
  | otherwise = oZ t

isUnitary :: [[Alpha]] -> Bool
isUnitary lists
  | oZ lists = True
  | otherwise   = let mat =  debug(show lists ++ "\n")
                              fromLists lists --Create matrix from lists
                      conjugateTranspose = fmap conjugate $ Data.Matrix.transpose mat --Conjugate Transpose Matrix
                      inverseMat = debug("ConjugateTranspose: \n" ++ show conjugateTranspose ++ "\n")
                                    wrap $ inverse mat --The inverse matrix
                      in if (conjugateTranspose) == inverseMat then debug("InverseMat: \n" ++ show inverseMat ++ "\n")
                                                                            True --Test unitarity
                         else debug("InverseMat: \n" ++ show inverseMat ++ "\n")
                                False










-- getLinearAlphas :: E -> [Alpha]
-- getLinearAlphas (Combination (AlphaVal a v1) v2) = a : getLinearAlphas v2
-- getLinearAlphas (Combination (Val v) v2) = (1 :+ 0) : getLinearAlphas v2 -- 1*CVal = CVal
-- getLinearAlphas (Val v) = (1 :+ 0):[]
-- getLinearAlphas (AlphaVal a _) = a:[]
-- getLinearAlphas (LetE _ _ _ e) = getLinearAlphas e
--
-- getLinearTerms :: [E] ->[[Alpha]]
-- getLinearTerms [] = []
-- getLinearTerms (e:elist) = getLinearAlphas e : getLinearTerms elist



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
