module MonadicInt where
import AbstractData
import Utils


import Data.Complex
import Data.List
import Data.Matrix -- Needs installing via Cabal
import Debug.Trace
import Data.Number.CReal
import Control.Monad.State


type TypingState = (Delta,Psi)

--Entry point for the tests from main.
typeCheck :: Delta -> Psi -> Iso -> T -> (Either TypeErrors T, TypingState)
typeCheck delta psi iso t = runState (isoTypeCheck iso t) (delta,psi)

--Retrieve the type of supplied value from context if it exists, otherwise return a TypeError
myxType :: String -> Maybe A -> Either TypeErrors A
myxType _ (Just v) = Right v -- Found the variable in the context, return its type
myxType x Nothing = Left $ VarError "Variable not in context: " x


xType :: Maybe A -> Either TypeErrors A
xType (Just v) = Right v -- Found the variable in the context, return its type
xType Nothing = Left $ VarError "Variable not in context" ""

--Lookup variable x in the supplied context. If variable is found, returns Just A, otherwise returns Nothing
xInContext :: String -> Delta -> Maybe A
xInContext x delta = lookup x delta -- Lookup :: a -> [(a,b)] -> Maybe b
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
valueTypes :: [V] -> A -> State TypingState (Either TypeErrors A)
valueTypes [] a = return $ Right a
valueTypes (v:vals) a = do
                          st1 <- valueTypeCheck v a
                          if (wrap $ st1 ) == a then debug("Value checked:" ++ show a)
                                                        valueTypes vals a
                          else debug("Values didnot match: " ++ show a)
                                return $ Left $ ValueError "Value V doesnt match supplied type" v a

--Implementar a função para verificar os tipos dos ExtendedValues!!
extendedValueTypes :: [E] -> B -> State TypingState (Either TypeErrors B)
extendedValueTypes [] b = return $ Right b
extendedValueTypes (e1:listE) b = -- debug ("extValTypes..")
                                  do
                                      st1 <- extendedValueTypeCheck e1 b
                                      if (b == wrap st1)
                                          then extendedValueTypes listE b
                                      else return $ Left $ CustomError "Extended Value not matching Type" (show e1 ++ " : "++ show b)

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

--Check if product and type provided are pairs. If so, extend the context
-- Otherwise return a typing error.
addToContext :: Delta-> P -> A -> Either TypeErrors Delta
addProductToContext delta (EmptyP) a = Right delta
addToContext delta (PairP (Xprod x) (Xprod y)) (Prod a b) = Right $ delta ++
                                                              (wrap $ addToContext delta (Xprod x) a) ++ (wrap $ addToContext delta (Xprod y) b)
addToContext delta (Xprod x) a = case (lookup x delta) of
                                  Nothing -> Right $ (x,a) : delta
                                  Just a'
                                    | a' == a -> Right delta
                                    | otherwise -> let (delta',_) = partition (\z -> fst z /= x) delta
                                                   in Right $ (x,a) : delta'
addToContext _ (PairP p1 p2) _ = Left $ ProdError "Not a product Type" (PairP p1 p2)



testUnit::[E]->Bool
testUnit = isUnitary . getLinearTerms

isUnitary :: [[Alpha]] -> Bool
isUnitary lists = let mat =  debug(show lists ++ "\n")
                              fromLists lists --Create matrix from lists
                      conjugateTranspose = fmap conjugate $ Data.Matrix.transpose mat --Conjugate Transpose Matrix
                      inverseMat = debug("ConjugateTranspose: \n" ++ show conjugateTranspose ++ "\n")
                                    wrap $ inverse mat --The inverse matrix
                      in if (conjugateTranspose) == inverseMat then debug("InverseMat: \n" ++ show inverseMat ++ "\n")
                                                                            True --Test unitarity
                         else debug("InverseMat: \n" ++ show inverseMat ++ "\n")
                                False



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

-- addProductToContext :: Delta -> P -> A -> Delta
-- addProductToContext delta (EmptyP) a = delta
-- addProductToContext delta (Xprod x) a = (x,a):delta
-- addProductToContext delta (PairP p1 p2) (Prod a b) = addProductToContext delta p1 a ++ addProductToContext delta p2 b








-- TypeChecking definition for terms
mytermTypeCheck :: Term -> A -> State TypingState (Either TypeErrors A)
mytermTypeCheck EmptyTerm a = return $ Right One
--IF variable x is in context with type matching a, return the type
mytermTypeCheck (XTerm x) a = do
                                (delta,_) <- debug ("Var:" ++ show a)
                                                get
                                return $ Right (wrap $ matchTypes a (XTerm x) $ wrap $ myxType x $ xInContext x delta)
--Typecheck term t and match resulting type with a. If it matches return a+b.
mytermTypeCheck (InjLt t) (Sum a b) = do
                                        st1 <- debug ("Injl:" ++ show a)
                                                  mytermTypeCheck t a
                                        return $ Right $ Sum (wrap $ matchTypes a t $ wrap st1) b
-- --Typing clause for Recursive list Types empty lists.
mytermTypeCheck (InjLt EmptyTerm) (Rec a) = return $ Right $ Rec a --Valid????
--Typecheck term t and match resulting type with b. If it matches return a+b.
mytermTypeCheck (InjRt t) (Sum a b) = do
                                        st1 <- debug ("InjR:" ++ show b)
                                                mytermTypeCheck t b
                                        return $ Right $ Sum a (wrap $ matchTypes b t $ wrap st1)
-- --TypeChecking clause for supporting Recursive list Types constructors (x:list)
mytermTypeCheck (InjRt (PairTerm t1 t2)) (Rec a) = do
                                                     a' <- mytermTypeCheck t1 a
                                                     recA <- mytermTypeCheck t2 (Rec a)
                                                     case wrap $ recA of
                                                       Rec r ->  if (wrap a' == a) then return $ Right $ Rec a
                                                                 else return $ Left $ CustomError "Constructor pair is wrong:" (show t1 ++ ":" ++ show t2 ++ show a)
                                                       otherwise -> return $ Left $ CustomError "Right element of cons not a list" (show (PairTerm t1 t2))
-- --Typecheck t1 with a, t2 with b. If they succeed, return a * b --On pairs: differentiating the contexts for each t is necessary?
mytermTypeCheck (PairTerm t1 t2) (Prod a b) = do
                                                st1 <- mytermTypeCheck t1 a
                                                st2 <- mytermTypeCheck t2 b
                                                return $ Right $ Prod (wrap st1) $ wrap st2
-- --Typecheck the iso f, match t with the first part of resulting type ("input"). If they match, return type b
mytermTypeCheck (Omega f t) b = do
                                  st1 <- isoTypeCheck f (Iso (TypeVar 'a') b)
                                  let isoInputType = wrap $ checkIsoReturnType b $ wrap $ st1
                                    in do
                                         st2 <- mytermTypeCheck t isoInputType
                                         if (wrap st2 == isoInputType) then return $ Right b
                                            else return $ Left $ OmegaError "Omega input of the wrong type" (Omega f t)
-- --Typecheck t1 and use resulting type to add variables from p to the context. Using the new context, typecheck t2 with type c.
mytermTypeCheck (Let p t1 t2) c = do
                                     st1 <- mytermTypeCheck t1 c
                                     (delta,psi) <- get
                                     let newDelta = wrap $ addToContext delta p $ wrap st1
                                      in do
                                            put (newDelta,psi)
                                            st2 <- mytermTypeCheck t2 c
                                            return $ Right $ wrap st2
mytermTypeCheck (CombTerms t1 t2) c = do
                                        st1 <- mytermTypeCheck t1 c
                                        st2 <- mytermTypeCheck t2 c
                                        if st1 == st2 then return $ Right c
                                        else return $ Left $ CustomError  "Term combination failed, terms not of same type:" (show t1 ++ ":" ++ show st1  ++ show t2 ++ ":" ++ show st2)
mytermTypeCheck (AlphaTerm a t) c = mytermTypeCheck t c -- Typechecking doesn't care about the alpha.
-- --Whenever typeChecking fails, return a Left value showing the matching error. Could make it more descriptive?
mytermTypeCheck t a = return $ Left $ CustomError "Cannot match term and type:" (show t ++ " : " ++ show a)
--

--TypeChecking for values, same behavior as termTypeCheck
valueTypeCheck ::  V -> A  -> State TypingState (Either TypeErrors A)
valueTypeCheck EmptyV One = return $ Right One
valueTypeCheck (Xval x) a = do
                              (delta,_) <- get
                              return $ Right (wrap $ matchTypes a (XTerm x) $ wrap $ myxType x $ xInContext x delta)
valueTypeCheck (InjL v) (Sum a b) = do
                                      st1 <- valueTypeCheck v a
                                      return $ Right $ Sum (wrap $ matchTypes a v $ wrap $ st1) b
valueTypeCheck (InjL (EmptyV)) (Rec a) = return $ Right $ Rec a -- ??????
valueTypeCheck (InjR v) (Sum a b) = do
                                      st1 <- valueTypeCheck v b
                                      return $ Right $ Sum a (wrap $ matchTypes a v $ wrap $ st1)
valueTypeCheck (InjR (PairV v1 v2)) (Rec a) = do
                                                a' <- valueTypeCheck v1 a
                                                recA <- valueTypeCheck v2 (Rec a)
                                                case wrap $ recA of
                                                  Rec r -> if (wrap a' == a) then return $ Right $ Rec a
                                                           else return $ Left $ CustomError "Constructor pair is wrong:" (show v1 ++ ":" ++ show v2 ++ show a)
                                                  otherwise -> return $ Left $ CustomError "Right element of cons not a list" (show (PairV v1 v2))
valueTypeCheck (PairV v v2) (Prod a b) = do
                                            st1 <- valueTypeCheck v a
                                            st2 <- valueTypeCheck v2 b
                                            return $ Right $ Prod (wrap $ st1) (wrap $ st2)
valueTypeCheck v a = return $ Left $ CustomError "Value matching failed:" (show v ++ ":" ++ show a)

--TypeChecking for special products cases. Not 100% ...
productsTypecheck :: P -> A ->State TypingState (Either TypeErrors A)
productsTypecheck (Xprod x) a = valueTypeCheck (Xval x) a
productsTypecheck (PairP p1 p2) (Prod a b) = do
                                                st1 <- productsTypecheck p1 a
                                                st2 <- productsTypecheck p2 b
                                                return $ Right $ Prod (wrap st1) $ wrap st2
productsTypecheck p _ = return $ Left $ CustomError "Product typechecking error" (show p)


-- --TypeChecking for extendedValues. ?
extendedValueTypeCheck :: E -> A -> State TypingState (Either TypeErrors A)
extendedValueTypeCheck (Val v) a = valueTypeCheck v a
extendedValueTypeCheck (LetE p1 iso p2 e) a = do
                                                (delta,psi) <- get
                                                let isoType = wrap $ getIsoTypes $ wrap $ isoTypeFromPsi $ isoLookup iso psi
                                                  in do
                                                        st1 <- productsTypecheck p2 $ fst isoType
                                                        if(fst isoType) == (wrap st1)
                                                          then let newDelta = wrap $ addToContext delta p1 $ snd isoType
                                                                  in do
                                                                        put(newDelta,psi)
                                                                        debug("LetExtVal: adding p1 to context:" ++ (show p1) ++ ": " ++ (show (snd isoType)))
                                                                          extendedValueTypeCheck e a
                                                        else return $ Left $ ProdError "Product not input of Iso" p2
extendedValueTypeCheck (Combination e1 e2) a = do
                                                  st1 <- extendedValueTypeCheck e1 a
                                                  st2 <- extendedValueTypeCheck e2 a
                                                  if (wrap st1) == (wrap st2) then return $ Right a
                                                  else return $  Left $ CustomError "Combination of extendedValues of differing types" ("e1:" ++ show st1 ++ " " ++ "e2:" ++ show st2)
extendedValueTypeCheck (AlphaVal alpha e) a = extendedValueTypeCheck e a

-- -- checkLinearCombinationExtVals :: Delta -> Psi -> E -> A -> Either TypeErrors A
-- -- checkLinearCombinationExtVals _ _ (Val []) a = Right a
-- -- checkLinearCombinationExtVals delta psi (Val alphaV:vals) a = if valueTypeCheck delta (snd alphaV) a == (Right a) then
-- --                                                                 checkLinearCombinationExtVals delta psi (Val vals) a
-- --                                                               else Left $ CustomError "Linear Combination of ExtVals failed typechecking" ""
--
-- -- TypeChecking function for isomorphisms.
isoTypeCheck :: Iso -> T -> State TypingState (Either TypeErrors T)
--Check that iso variable is in the context with matching type t.
isoTypeCheck (IsoVar f) (Iso (TypeVar a) b) = do
                                                (_,psi) <- get
                                                return $ Right $ wrap $ fType f $ fInContext f psi -- Case where variable is an already typed function. Eg: Iso application f (g term), f needs to be an already declared iso.
isoTypeCheck (IsoVar f) t = do
                              (_,psi) <- get
                              return $ Right $ wrap $ matchIsoTypes t (IsoVar f) $ wrap $ fType f $ fInContext f psi
--Add isoVariable f to context with type (a<->b) and typeCheck iso with resulting context and type t
isoTypeCheck (Lambda f iso) (Comp a b t) = do
                                              (delta,psi) <- get
                                              let newPsi = addIsoNameToPsi psi f (Iso a b)
                                                in do
                                                    put (delta,newPsi)
                                                    st1 <- isoTypeCheck iso t
                                                    return $ Right $ Comp a b $ wrap st1
--Iso application. Since isos don't carry type annotations, typecheck iso1 with a dummy type consisting of TypeVars in order to get back the real type
isoTypeCheck (App iso1 iso2) t = do
                                    st1 <- isoTypeCheck iso1 $ Comp (TypeVar 'a') (TypeVar 'b') t
                                    let iso1Type = breakIsoType $ wrap st1
                                        iso1Left = fst iso1Type
                                        iso1Right = snd iso1Type
                                      in do
                                          st2 <- isoTypeCheck iso2 iso1Left
                                          if (wrap st2) == iso1Left && iso1Right == t then return $ Right t
                                          else return $ Left $ AppError "Cannot app isos" iso1 iso2
--Get lists of values and extendedValues and typeCheck them. If they are not all of the same value, wrap will catch it.
--Create the orthogonal decomposition sets for both lists, if the creation fails we get a Left value caught by wrap.
--Test that the values match Type a and extendedValues match type b. If so, typechecking succeeds, else we return an error.
isoTypeCheck (Clauses list) (Iso a b) = do
                                           (delta,_) <- get
                                           let  vList = map fst list
                                                eList = map snd list
                                                odA = wrap $ orthogonalDecomposition delta a [] vList --NEED TO INPUT A TEST CASE FOR OrthogonalDecomps. Not sure they are being evalueated
                                                odB = wrap $ extOrthogonalDecomposition delta b [] eList
                                                unitary = testUnit eList
                                             in do
                                                  vTypes <- valueTypes vList a
                                                  eTypes <- extendedValueTypes eList b
                                                  if (wrap eTypes) == b && (wrap vTypes) == a then
                                                      if(unitary) then return $ Right $ Iso a b
                                                      else return $ Left $ IsoError "Not a unitary Matrix!" "\n" (show (Clauses list))
                                                  else return $ Left $ IsoError "Iso Clausess dont match type:" (show (Clauses list)) (show (Iso a b))--Need to garantee correct checking of vals and extVals still
-- --Typecheck Fixpoints here.
isoTypeCheck (Fixpoint f iso) t =do
                                    (delta,psi) <- get
                                    let newPsi = addIsoNameToPsi psi f t
                                      in do
                                            put (delta,newPsi)
                                            if fixpointTerminates psi (Fixpoint f iso) -- Not implemented.
                                              then isoTypeCheck iso t
                                            else return $ Left $ FixpointError "Fixpoint does not terminate: " (show (Fixpoint f iso))
--                                   --If Fixpoint terminates in a finite context, then:
--                                 --Right (Comp a b $ wrap $ isoTypeCheck delta (addIsoNameToPsi psi f (Iso a b)) iso (Comp a b t))
-- --If typeChecking fails return a Left value with an error.
isoTypeCheck iso t = return $ Left $ IsoError "Could not match supplied iso" (show iso) (show t)

--Check fixpoint termination...
fixpointTerminates :: Psi -> Iso -> Bool
fixpointTerminates _ _ = True
