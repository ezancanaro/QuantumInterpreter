{-# LANGUAGE ParallelListComp #-}
module Semantics where
import AbstractData
import Utils

import Data.Number.CReal
import Data.Complex
import Data.List
import Data.Matrix -- Needs installing via Cabal
-----------------------------------------------------------------------------------------------------------------------------
------------------Semantics---------------
-----------------------------------------------------------------------------------------------------------------------------
type Sigma = [(String,V)]


support :: Sigma -> [String]
support [] = []
support (vx:sigma) = fst vx : support sigma


intersectionTest :: (Sigma->[String]) -> Sigma -> Sigma -> [String]
intersectionTest f sig1 sig2 = (f sig1) `intersect` (f sig2)

--Starting point for evaluating terms. Since every program could potentially generate a combination we always apply these properties.
startEval :: Term -> V
startEval t = fullyReduce $ (algebraicProperties . distributiveProp) $ applicativeContext t

-- Make sure combinations are fully reduced before returning them.
-- Should be able to eliminate this function call by properly dealing with these results in the distributiveProp function, but I can't for the life of me figure it out there, so I need to add this stupid little function to make sure it works properly and ramble on a stupid comment to alleviate the feeling of being kinda dumb, but not that dumb.
fullyReduce :: E -> V
fullyReduce e = if combFullyReduced $ e
                  then removeEV $ Evalue e
                  else fullyReduce $ (algebraicProperties . distributivePropExtended) e

-- maybe sig1 . maybe sig2

matching:: Sigma -> V -> V -> Maybe Sigma
matching sigma EmptyV EmptyV = Just sigma
matching sigma (Xval x) w = Just $ (x,w) : sigma
matching sigma (InjL v) (InjL w) = matching sigma v w
matching sigma (InjR v) (InjR w) = matching sigma v w
matching sigma (PairV v1 v2) (PairV w1 w2) = let  sig1 = matching sigma v1 w1
                                                  sig2 = matching sigma v2 w2
                                             in case (sig1,sig2) of
                                                  (Just sigma1,Just sigma2) -> case intersectionTest support sigma1 sigma2 of
                                                                                    [] -> --debug("Actually succedded")
                                                                                            Just $ sigma1 `union` sigma2
                                                                                    otherwise -> --debug("Support intersects:" ++ show sigma1 ++ "||" ++ show sigma2)
                                                                                                    Nothing -- error $ ("Support Intersects: " ++ show sigma1 ++"\n"++ show sigma2)
                                                  _ -> --debug("Falied to match pair to value::" ++ show (PairV w1 w2))
                                                         Nothing
matching sigma term (Evalue (Val v)) = matching sigma term v -- Need this so let expressions work properly.
matching sigma term (Evalue (AlphaVal 1 (Val v))) = matching sigma term v -- A value with amplitude 1 is just the value itself
matching _ term val = --debug ("Tried matching: " ++ show term ++ "//With: " ++ show val)
                        Nothing



applicativeContext :: Term -> V
applicativeContext EmptyTerm = EmptyV
applicativeContext (XTerm x) = Xval x
applicativeContext (InjLt t) = InjL $ applicativeContext t
applicativeContext (InjRt t) = InjR $ applicativeContext t
applicativeContext (PairTerm t1 t2) = PairV (applicativeContext t1) $ applicativeContext t2
applicativeContext (Omega iso t) = reductionRules $ Omega iso $ ValueT $ applicativeContext t
                                    --Reduce t to a value and apply it to iso
applicativeContext (Let p t1 t2) = let v = ValueT $ applicativeContext t1
                                      in reductionRules (Let p v t2)
applicativeContext (ValueT v) = v

reductionRules :: Term -> V
reductionRules (Let p (ValueT v1) t2) = replace t2 $ catchMaybe errorString $ matching  [] (productVal p) v1
                                          where errorString = "Failed pattern-matching on let " ++ show p ++ " = " ++ show v1
reductionRules (Omega (Clauses isoDefs) (ValueT (PairV v1 v2))) = if isVlinear (PairV v1 v2) --then error "Undefined"
                                                                    then reductionRules (Omega (Clauses isoDefs) (ValueT $ Evalue $ distributiveProp (PairV v1 v2)))
                                                                    else applyValueToClauses (Clauses isoDefs) (ValueT (PairV v1 v2))
reductionRules (Omega (Clauses isoDefs) (ValueT (Evalue e))) = --debug("Matching eval..")
                                                                  wrap $ matchLinearCombinations isoDefs e 1
reductionRules (Omega (Clauses isoDefs) (ValueT v)) = applyValueToClauses (Clauses isoDefs) (ValueT v)
                                      --Iso application: In case iso1 is a lambda, substitute the free-vars for iso2 and then apply term to it
reductionRules (Omega (App i1 i2) t) = reductionRules (Omega (isoReducing (App i1 i2)) t)
reductionRules (Omega (Fixpoint f (Clauses isoDefs)) (ValueT v)) = let unfoldedRecursion = --debug ("My Val: " ++ show v)
                                                                                              buildLamFromFix f v (Clauses isoDefs)
                                                                       in reductionRules (Omega unfoldedRecursion (ValueT v))

--                                                                        i = snd match
--                                                                        term = --debug ("i: " ++ show i ++ "lista: " ++ show (length isoDefs))
--                                                                                  snd $ isoDefs !! i
--                                                                        in --debug("Chosen:  "++ show (fst match) ++ " to: " ++ show term)
--                                                                           if checkIfFixedPoint term f then reduceE (fst match) term
--                                                                           else reductionRules (Omega (isoReducing (Fixpoint f (Clauses isoDefs))) (ValueV t))
--                                                                                     --not correct
reductionRules t = error $ "Failed to reuce: " ++ show t

--Function to apply simple values to isos
applyValueToClauses :: Iso -> Term -> V
applyValueToClauses (Clauses isoDefs) (ValueT v) = let match = matchClauses isoDefs v 0 -- NOT COMPLETED YET
                                                       i = snd match
                                                   in if i < length isoDefs
                                                      then let term = --debug ("i: " ++ show i ++ "lista: " ++ show (length isoDefs))
                                                                            snd $ isoDefs !! i
                                                               in --debug("Chosen:  "++ show (fst match) ++ " to: " ++ show term)
                                                                        reduceE (fst match) term
                                                      else error $ "Failed to match value: " ++ show v ++ " in clauses:\n" ++ (show $ map fst isoDefs)

-- applyLinearCombinationsInPairs :: Iso -> V -> V
-- applyLinearCombinationsInPairs (Clauses isoDefs) (PairV v1 v2) = let tensor = Evalue $ distributiveProp $ PairV v1 v2
--                                                                  in reductionRules (Clauses isoDefs) tensor

-- <a1 + a2, b1 + b2> -> a1.b1<a1,b1>+a1.b2<a1,b2>+a2.b1<a2,b1>+a2.b2<a2,b2>
-- <a1+a2, <b1+b2,c1+c2> -><a1+a2, b1.c1<b1,c1> + b1.c2<b1,c2> + b2.c1<b2,c1> + b2.c2<b2,c2>
--   -> a1.b1.c1<a1,<b1,c1> + a1.b1.c2<a1,<b1,c2> + a1.b2.c1<a1,<b2,c1> + a1.b2.c2<a1,<b2,c2> + a2....

--The next two functions are needed due to unorganized implementation of distributiveProp, in order to avoid infinite loops on evaluation.
replaceVP :: V -> V -> V
replaceVP new (EmptyV) = EmptyV
replaceVP new (Xval "stupidVariable") = new
replaceVP new (InjL v) = InjL $ replaceVP new v
replaceVP new (InjR v) = InjR $ replaceVP new v
replaceVP new (PairV v1 v2) = PairV (replaceVP new v1) (replaceVP new v2)
replaceVP new (Evalue (Val v)) = replaceVP new v

replaceVarForPair :: V -> E -> E
replaceVarForPair v (Val v') = Val $ replaceVP v v'
replaceVarForPair v (Combination e1 e2) = Combination (replaceVarForPair v e1) (replaceVarForPair v e2)
replaceVarForPair v (AlphaVal a e) = AlphaVal a $ replaceVarForPair v e

-- Taking a value pair containing at least one linear combination and translating it to the tensorProduct representation of states.
-- This function is needed to allow pattern matching on applications such as: Cnot <0+1/sqrt(2),0+1/sqrt(2)>
-- The example would be applied in the form: Cnot (1/sqrt(2)*1/sqrt(2)<0,0> + 1/sqrt(2)*1/sqrt(2)<0,1> + 1/sqrt(2)*1/sqrt(2)<1,0> + 1/sqrt(2)*1/sqrt(2)<1,1>)
distributiveProp :: V -> E
distributiveProp (PairV (Evalue e1) (PairV v1 v2)) = -- -- Infinite loop when PairV v1 v2 is normalized, but Evale e is not.
                                                      if tensorPair /= PairV v1 v2
                                                        then --debug ("tensor1:: " ++ show (PairV (Evalue e1) (PairV v1 v2)) ++ "\n")
                                                                distributiveProp (PairV (Evalue e1) tensorPair)
                        --We substitute the pair for a variable to avoid infinite recursion choosing this same pattern in every evaluation. This is a stupid solution, hence the name of the variable.
                                                        else replaceVarForPair (PairV v1 v2) $ distributiveProp (PairV (Evalue e1) (Xval "stupidVariable"))
                                                        where tensorPair = removeEV $ Evalue $ distributiveProp $ PairV v1 v2
-- Defining this case for the sake of completeness, but the interpreter should default to representing tuples as <v,<v2,v3>>.
-- Need to make this clear when building the parser to allow the <v1,v2,...,vn> syntax.
distributiveProp (PairV (PairV v1 v2) (Evalue e1) ) = ----debug ("tensor2:: " ++ show (PairV (PairV v1 v2) (Evalue e1)) ++ "\n")
                                                        if tensorPair /= PairV v1 v2
                                                          then --debug ("tensor1:: " ++ show (PairV (Evalue e1) (PairV v1 v2)) ++ "\n")
                                                                distributiveProp (PairV tensorPair (Evalue e1))
                          --We substitute the pair for a variable to avoid infinite recursion choosing this same pattern in every evaluation. This is a stupid solution, hence the name of the variable.
                                                          else replaceVarForPair (PairV v1 v2) $ distributiveProp (PairV (Xval "stupidVariable") (Evalue e1))
                                                          where tensorPair = removeEV $ Evalue $ distributiveProp $ PairV v1 v2
distributiveProp (PairV (Evalue e1) (Evalue e2))
  | AlphaVal (1:+0) (Val v1) <- e1 = distributiveProp (PairV v1 $ removeEV (Evalue e2)) --Casting of val to eval is really annoying in this iplementation.
  | AlphaVal (1:+0) (Val v2) <- e2 = distributiveProp (PairV (removeEV (Evalue e1)) v2)
  | otherwise = let  c1 = pairAlphasWithValues True e1
                     c2 = pairAlphasWithValues True e2
                 in --debug ("tensor3:: " ++ show (PairV (Evalue e1) (Evalue e2)) ++ "\n")
                      combPairs (pairThem c1 c2)
distributiveProp (PairV (Evalue e1) v2) =  let c1 = pairAlphasWithValues True (distributivePropExtended $ removeVE e1)
                                               c2 = [((1:+0), distributiveProp v2)]
                                               in  --debug ("tensor4:: " ++ show (PairV (Evalue e1) v2) ++ "\n")
                                                    combPairs (pairThem c1 c2)
distributiveProp (PairV v2 (Evalue e1)) =  let c1 = [((1:+0), distributiveProp v2)]
                                               c2 = pairAlphasWithValues True (distributivePropExtended $ removeVE e1)
                                               in  --debug ("tensor5:: " ++ show (PairV v2 (Evalue e1)) ++ "\n")
                                                    combPairs (pairThem c1 c2)
distributiveProp (Evalue e)= --debug ("tensor6:: " ++ show (Evalue e) ++ "\n")
                                distributivePropExtended e
distributiveProp (PairV v1 v2) =
                                if containsAmplitude v1
                                    then Val $ PairV (removeEV $ Evalue $ distributiveProp v1) (v2)
                                else Val $ PairV v1 v2
  --Val $ PairV v1 v2
--Treating lists of linear combination:
distributiveProp (InjR (PairV v1 v2)) =
                                        if thisTensor == Val (InjR (PairV v1 v2))
                                          then --debug("TensorListStopped" ++ show (PairV v1 v2))
                                                thisTensor
                                          else --debug("TensorList " ++ show (PairV v1 v2))
                                                distributivePropExtended thisTensor
                                        where thisTensor = listCombsToCombLists (InjR $ removeEV $ Evalue $ distributiveProp (PairV v1 v2))
distributiveProp (InjL EmptyV) = Val $ InjL EmptyV
distributiveProp v = --debug("Tensor Nada")
                      Val $ v
--distributiveProp v = error $ "TensorRep undefined for: " ++ show v

containsAmplitude :: V -> Bool
containsAmplitude (Evalue e)
  | Combination e1 e2 <- e = True
  | AlphaVal a e1 <- e = True
  | otherwise = False
containsAmplitude (InjR v) = containsAmplitude v
containsAmplitude (InjL v) = containsAmplitude v
containsAmplitude (PairV v1 v2) = containsAmplitude v1 || containsAmplitude v2
containsAmplitude x = False

--THe implementation tends to generate a lot of (Evalue (Val v)) terms, this functions gets rid of them
removeEV :: V -> V
removeEV (Evalue (Val v)) = v
removeEV v = v

removeVE :: E -> E
removeVE (Val (Evalue e)) = e
removeVE e = e


distributivePropExtended :: E -> E
distributivePropExtended (Val (Evalue e)) = distributivePropExtended e
distributivePropExtended (Val v) = distributiveProp v
distributivePropExtended (AlphaVal a (Val (PairV v1 v2))) = algebraicProperties $ AlphaVal a (distributiveProp $ PairV v1 v2)
distributivePropExtended (AlphaVal a (Val (InjR v)))
  | (Evalue (Val (PairV v1 v2))) <- v = distributivePropExtended $ AlphaVal a (Val (InjR (PairV v1 v2)))
  | (PairV v1 v2) <- v,
    a == (1:+0) = distributiveProp (InjR (PairV v1 v2))
  | (PairV v1 v2) <- v, --Treat it as normal pair of combinations and readd the list constructor after.
    a /= (1:+0) = readdListCons $ algebraicProperties $ AlphaVal a (distributiveProp $ PairV v1 v2)
  | otherwise = AlphaVal a (distributivePropExtended (Val (InjR v)))
distributivePropExtended (AlphaVal a e) = AlphaVal a (distributivePropExtended e) --
distributivePropExtended (Combination e1 e2) = Combination (distributivePropExtended e1) (distributivePropExtended e2)--
  --These cases are needed to make sure that we don't stop before working on the outrer layer of a list. Without them we stop at: 0.3[InjL,0.5[x,y]+0.5[z,w]]
  --Without proper guards we get ourselves into an infinite recursion. SAD.
distributivePropExtended e = e

combFullyReduced :: E -> Bool
combFullyReduced (Combination e1 e2)
  --General values
  | AlphaVal a (AlphaVal b e) <- e1 = False
  | AlphaVal a (AlphaVal b e) <- e2 = False
  | AlphaVal a (Combination e3 e4) <- e1 = False
  | AlphaVal a (Combination e3 e4) <- e2 = False
  | Combination e3 e4 <- e1,
    Combination e5 e6 <- e2 = combFullyReduced e1 && combFullyReduced e2 -- Both are combinations
  | Combination e3 e4 <- e1 = combFullyReduced e1 -- Only e1 is combination
  | Combination e3 e4 <- e2 = combFullyReduced e2 -- Only e2 is combination
  -- Lists::
  | AlphaVal a (Val (InjR (PairV v1 v2))) <- e1
      = case v1 of
          Evalue e  -> False
          otherwise -> case v2 of
                          Evalue e  -> False
                          otherwise -> True
  | AlphaVal a (Val (InjR (PairV v1 v2))) <- e2
      = case v1 of
          Evalue e  -> False
          otherwise -> case v2 of
                          Evalue e  -> False
                          otherwise -> True
  | AlphaVal a (Val (PairV v1 v2)) <- e1
      = case v1 of
          Evalue e  -> False
          otherwise -> case v2 of
                          Evalue e  -> False
                          otherwise -> True
    | AlphaVal a (Val (PairV v1 v2)) <- e2
        = case v1 of
            Evalue e  -> False
            otherwise -> case v2 of
                            Evalue e  -> False
                            otherwise -> True
  | otherwise =  debug ("FullyReduced: " ++ show (Combination e1 e2))
                    True
combFullyReduced (AlphaVal a (AlphaVal b e)) = False
combFullyReduced e = True

listCombsToCombLists :: V -> E
listCombsToCombLists (InjR (Evalue c))
  | Combination (AlphaVal a1 e1) (AlphaVal a2 e2) <- c = Combination (AlphaVal a1 (Val $ InjR $ Evalue e1)) ((AlphaVal a2 (Val $ InjR $ Evalue e2)))
  | AlphaVal (1:+0) e <- c = Val $ InjR $ removeEV $ Evalue e
  | AlphaVal a e <-c = AlphaVal a $ Val $ InjR $ removeEV $ Evalue e
listCombsToCombLists (InjR v) = Val $ InjR v
-- listCombsToCombLists (InjL EmptyV) = Val $ InjL EmptyV
listCombsToCombLists e = error $ "Tensor of lists error on value: " ++ show e

readdListCons :: E -> E
readdListCons (AlphaVal a e1) = AlphaVal a (Val (InjR $ removeEV $ Evalue e1))
readdListCons (Combination e1 e2) = Combination (readdListCons e1) (readdListCons e2)
readdListCons (Val v) = Val $ InjR v

  ---0.707~<InjR_(),1~InjL_()>+0.707~<InjR_(),1~InjR_()> == <injR(),-0.707~InjL()+0.707InjR()>
  --Not really a needed function, but it could be usefull for presenting results
-- equivalentStates :: E -> E
-- equivalentStates (Combination (AlphaVal a1 e1) (AlphaVal a2 e2))
--   | Val (PairV v1 v2) <- e1,
--     Val (PairV v3 v4) <- e2,
--     v1 == v3
--       =   let av2 = AlphaVal a1 (Val v2)
--               av4 = AlphaVal a2 (Val v4)
--               in Val $ PairV v1 (Evalue $ Combination av2 av4)
--   | Val (PairV v1 v2) <- e1,
--     Val (PairV v3 v4) <- e2,
--     v2 == v4
--       =   let av1 = AlphaVal a1 (Val v1)
--               av3 = AlphaVal a2 (Val v3)
--               in Val $ PairV (Evalue $ Combination av1 av3) v2
--   | otherwise = Combination (AlphaVal a1 e1) (AlphaVal a2 e2)
-- equivalentStates (Val (Evalue e)) = equivalentStates e
-- equivalentStates (AlphaVal a e) = error $ "Why is it here? " ++ show e
-- equivalentStates (Combination (AlphaVal 0 e1) e2) = equivalentStates e2
-- equivalentStates (Combination e1 (AlphaVal 0 e2)) = equivalentStates e1
-- equivalentStates (Combination e1 e2)
--   | Val (Evalue e) <- e1 = equivalentStates $ Combination e e2
--   | Val (Evalue e) <- e2 = equivalentStates $ Combination e1 e
--   | otherwise = error $ "I can't really understand it." ++ show (Combination e1 e2)
-- equivalentStates e = error $ "Trouble applying EquivalentStates to: " ++ show e



pairThem :: [(Alpha,E)] -> [(Alpha,E)] -> [((Alpha,E),(Alpha,E))]
pairThem (x)(y) = [ (p1,p2) | p1<-x, p2<-y ]

combPairs :: [((Alpha,E),(Alpha,E))] -> E
combPairs (((a1,e1),(a2,e2)):[]) = AlphaVal (a1*a2) (Val (PairV (removeEV $ Evalue e1) (removeEV $ Evalue e2)))
combPairs (((a1,e1),(a2,e2)):list) = Combination comb1 (combPairs list)
                                    where comb1 = AlphaVal (a1*a2) (Val (PairV (removeEV $ Evalue e1) (removeEV $ Evalue e2)))

isVlinear :: V -> Bool
isVlinear (InjL v) = isVlinear v
isVlinear (InjR v) = isVlinear v
isVlinear (PairV v1 v2) = if not $ isVlinear v1
                            then isVlinear v2
                            else True
isVlinear (Evalue (AlphaVal _ _)) = True
isVlinear (Evalue (Combination _ _)) = True
isVlinear _ = False

buildLamFromFix :: String -> V -> Iso -> Iso
buildLamFromFix f v fix = let listLams = findFixedPoint f 0 v fix
                              fix' = renameInFixedPoint f 0 fix
                              fixedNameIsoPairs = findFixedPoint f 0 v fix
                              (names,isos) = listsFromPairs fixedNameIsoPairs
                              lambdaChain = lambdaBuilding names fix'
                              appChain = --debug ("Lams: " ++ show lambdaChain ++ "\n------------\n")
                                            appBuilding (reverse isos) lambdaChain
                              in --debug ("::: " ++ show appChain ++ "\n------------\n")
                                   appChain

lambdaBuilding :: [String] -> Iso -> Iso
lambdaBuilding [] fix = fix
lambdaBuilding (f:names) fix = Lambda f (lambdaBuilding names fix)

appBuilding :: [Iso] -> Iso -> Iso
appBuilding [] lambdaChain = lambdaChain
appBuilding (iso:isos) lambdaChain = App (appBuilding isos lambdaChain) iso


findFixedPoint :: String -> Int -> V -> Iso -> [(String,Iso)]
--CaseS of empty list
findFixedPoint f i (InjL EmptyV) fix = let fix' = renameInFixedPoint f (i+1) fix
                                           pairNameIso = ((f ++ show i), renameIsoVars i fix')
                                           in --debug ("fix': " ++ show fix' ++ " || pair: " ++ show pairNameIso ++ "\n------------\n")
                                                [pairNameIso] -- error ("EmptyV")
-- findFixedPoint f i (PairV list _) fix = let fix' = renameInFixedPoint f (i+1) fix
--                                             pairNameIso = ((f ++ show i), renameIsoVars i fix')
--                                             in --debug ("fix': " ++ show fix' ++ " || pair: " ++ show pairNameIso ++ "\n------------\n")
--                                                 [pairNameIso] -- error ("PAIRV")
findFixedPoint f i (PairV (InjL v) _) fix = findFixedPoint f i (InjL v) fix
findFixedPoint f i (PairV (InjR v) _) fix = findFixedPoint f i (InjR v) fix
findFixedPoint f i (PairV _ v2) fix = findFixedPoint f i v2 fix -- Allowing lists to be put at the end of a tuple.
-- --Cases where we apply a tuple of linear combinations on a fix-point iso.
-- findFixedPoint f i (InjR (PairV (Evalue e) t)) fix = findFixedPoint f i (Evalue $ distributiveProp (PairV (Evalue e) t)) fix
--Case of a list with elements -- Need to keep unfolding the iso.
findFixedPoint f i (InjR (PairV h t)) fix
  | Evalue (Val v') <- h = findFixedPoint f i (InjR (PairV v' t)) fix
  | Evalue (Val v') <- t = findFixedPoint f i (InjR (PairV h v')) fix
  |otherwise                              = let fix' = renameInFixedPoint f (i+1) fix
                                                pairNameIso = ((f ++ show i), renameIsoVars i fix')
                                                in --debug ("fix': " ++ show fix' ++ " || pair: " ++ show pairNameIso ++ "\n------------\n")
                                                    pairNameIso : findFixedPoint f (i+1) t fix
findFixedPoint f i (InjR (Evalue (Val v))) fix = findFixedPoint f i (InjR v) fix
--Special case for applying a Linear Combination to a fixPoint.
--Since amplitudes are not taken into consideration when pattern-matching values, we ignore them to create the proper unfolded function.
findFixedPoint f i (Evalue e) fix = findFixedPoint f i v fix
                                      where v = catchMaybe ("Failed to find fixed point of " ++ show e)$ extractValue e
findFixedPoint f i v iso = error $ "Cannot find fixPoint when applying to value: " ++ show v --Just in case of unexpected behavior. Should never arise.

--  Looks at values from a linear combination in order to build the unfolded recursive Iso.
-- A linear combination of lists will have every list be of the same size?? I don't think so. If size can vary, this implementation is not sufficient. Otherwise, this is fine.
-- Being the former, we need to look inside the combinations, using the longest list as the fixedPoint of the iso.
-- A second option is getting a different unfolded iso for each list, getting performance to tank hard.
extractValue :: E -> Maybe V
extractValue (Val (Evalue e)) = extractValue e
extractValue (Val v) = Just v
extractValue (AlphaVal 0 e) = Nothing
extractValue (AlphaVal a e) = extractValue e
extractValue (Combination e1 e2) = case extractValue e1 of --
                                      Nothing -> extractValue e2
                                      Just v -> Just v

renameInFixedPoint :: String -> Int -> Iso ->Iso
renameInFixedPoint f i (Clauses listVE) = let elist = fmap snd listVE
                                              vlist = fmap fst listVE
                                              in Clauses $ makePairs vlist $ renameFixInE f i elist
renameInFixedPoint _ _ iso = error ("Renaming: " ++ show iso)


renameFixInE :: String -> Int -> [E] -> [E]
renameFixInE _ _ [] = []
renameFixInE f i (e:elist) = rename f i e : renameFixInE f i elist

rename :: String -> Int -> E -> E
rename f i (LetE p1 (IsoVar f') p2 e)
  | f' == f = LetE p1 (IsoVar (f ++ show i)) p2 (rename f i e)
  | otherwise = LetE p1 (IsoVar f') p2 (rename f i e)
rename f i (LetE p1 iso p2 e) = LetE p1 (renameInFixedPoint f i iso) p2 (rename f i e) -- Not sure about this actually.
rename f i (Combination e1 e2) = Combination (rename f i e1) (rename f i e2)
rename f i e = e


makePairs :: [V] -> [E] -> [(V,E)]
makePairs (v:vlist) (e:elist) = (v,e) : makePairs vlist elist
makePairs [] [] = []
makePairs _ _ = error "Trying to pair different numbers of V and E"
  --Clauses (listV , renameF f i (map $ snd listE))

renameIsoVars :: Int -> Iso -> Iso
renameIsoVars i (Clauses listVE) = let (vlist,elist) = listsFromPairs listVE
                                       --elist = fmap snd listVE
                                       --vlist = fmap fst listVE
                                       in Clauses $ makePairs (renameVars i vlist) $ renameVarsE i elist


renameVars :: Int -> [V] -> [V]
renameVars _ [] = []
renameVars i vlist = map (renameVar i) vlist

renameVar :: Int -> V -> V
renameVar i (Xval var) = Xval (var ++ show i)
renameVar i (InjL v) = InjL $ renameVar i v
renameVar i (InjR v) = InjR $ renameVar i v
renameVar i (PairV v1 v2) = PairV (renameVar i v1) (renameVar i v2)
renameVar _ v = v

renameVarsE :: Int -> [E] -> [E]
renameVarsE _ [] = []
renameVarsE i elist = map (renameVarE i) elist

renameVarE :: Int -> E -> E
renameVarE i (Val v) = Val $ renameVar i v
renameVarE i (LetE p1 iso p2 e) = LetE (renameVarP i p1) iso (renameVarP i p2) (renameVarE i e)
renameVarE i (Combination e1 e2) = Combination (renameVarE i e1) (renameVarE i e2)
renameVarE i (AlphaVal alpha e) = AlphaVal alpha (renameVarE i e)

renameVarP :: Int -> P -> P
renameVarP i (Xprod var) = Xprod (var ++ show i)
renameVarP i (PairP p1 p2) = PairP (renameVarP i p1)  (renameVarP i p2)
renameVarP _ p = p
--
--


replace::  Term -> Sigma -> V
replace (EmptyTerm) sig= EmptyV
replace (XTerm x) sig  = case lookup (x) sig of
                          Nothing -> error $ "Did not find VariableTerm: " ++ show x ++ "in context: " ++ show sig--This is wrong!
                          Just v -> v
replace (InjLt v) sig  = InjL $ replace v sig
replace (InjRt v) sig  = InjR $ replace v sig
replace (PairTerm v1 v2) sig  = PairV (replace v1 sig) (replace v2 sig)


replaceV:: V -> Sigma ->V
replaceV (Xval x) sig = case lookup (x) sig of
                          Nothing -> error $ "Did not find Variable: " ++ show x ++ " in context: " ++ show sig--This is wrong!
                          Just v -> --debug ("Value: " ++ show v ++ "\n------------\n")
                                      v
replaceV (PairV v1 v2) sig = PairV (replaceV v1 sig) (replaceV v2 sig)
replaceV (InjR v) sig = InjR $ replaceV v sig
replaceV (InjL v) sig = InjL $ replaceV v sig
replaceV v _ = v -- Values that don't need substitution (EmptyV)


replaceInE :: E -> Sigma -> V
replaceInE (Val v) sig = v
replaceInE (LetE p iso p2 e) sig = EmptyV

--Replace cannot evaluate the expression. How does it return a value then?? It cannot return a LetValue
-- matchingP p1 $ evaluate iso $ replaceInP p2 sigma $ replaceInE e sig

-- let v = ValueT $ applicativeContext t1
  -- in reductionRules (Let p v t2)

replaceInP :: P -> Sigma -> V
replaceInP (EmptyP) sig = EmptyV
replaceInP (Xprod x) sig = replace (XTerm x) sig --Check that this is actually right
replaceInP (PairP p1 p2) sig = PairV (replaceInP p1 sig) (replaceInP p2 sig)


distributiveLetp :: Sigma -> P -> E -> E -> E
distributiveLetp sigma p (Combination (AlphaVal a e1) (Combination e2 e3)) bottom =
      let sig1 = catchMaybe errorString $ matching [] (productVal p) $ Evalue e1
          let1 = AlphaVal a $ Val $ reduceE (sig1++sigma) bottom
          let2 = distributiveLetp sigma p (Combination e2 e3) bottom
      in Combination let1 let2
          where errorString = "-Failed to reduce LetE: " ++ show p ++ " = " ++ show e1
distributiveLetp sigma p (Combination (Combination e2 e3) (AlphaVal a e1)) bottom =
      let sig1 = catchMaybe errorString $ matching [] (productVal p) $ Evalue e1
          let1 = AlphaVal a $ Val $ reduceE (sig1++sigma) bottom
          let2 = distributiveLetp sigma p (Combination e2 e3) bottom
      in Combination let1 let2
          where errorString = "0-Failed to reduce LetE: " ++ show p ++ " = " ++ show e1
distributiveLetp sigma p (Combination (AlphaVal a e1) (AlphaVal b e2)) bottom =
      let sig1 = catchMaybe errorString $ matching [] (productVal p) $ removeEV (Evalue e1)
          sig2 = catchMaybe errorString2 $ matching [] (productVal p) $ removeEV (Evalue e2)
          let1 = AlphaVal a $ Val $ reduceE (sig1++sigma) bottom
          let2 = AlphaVal b $ Val $ reduceE (sig2++sigma) bottom
          in Combination let1 let2
              where errorString = "1-Failed to reduce LetE: " ++ show p ++ " = " ++ show  (AlphaVal a e1)
                    errorString2 = "2-Failed to reduce LetE: " ++ show p ++ " = " ++ show e2
distributiveLetp sigma p (Combination e1 e2) bottom
  | Val v1 <- e1 = distributiveLetp sigma p (Combination (AlphaVal (1:+0) (Val v1)) e2) bottom
  | Val v2 <- e2 = distributiveLetp sigma p (Combination e1 (AlphaVal (1:+0) (Val v2))) bottom
distributiveLetp s p e b = error $ "undefined operation on " ++ show s ++ show p ++ show e

reduceE :: Sigma -> E -> V
reduceE sigma (LetE (Xprod s) iso p2 e) = let v = replaceInP p2 sigma
                                              v' = startEval (Omega iso (ValueT v))
                                              sig2 = --debug("Pair: " ++ show (Xprod s) ++ "  Value:" ++ show v')
                                                        catchMaybe errorString $ matching [] (productVal (Xprod s)) v'
                                                          where errorString = "Failed to match on LetE: " ++ show (Xprod s) ++ " = " ++ show v'
                                              in --debug("V: " ++ show v ++ " V': " ++ show v' ++ " Sig2: " ++ show sig2)
                                                              reduceE (sig2++sigma) e
reduceE sigma (LetE p iso p2 e) = let   v = replaceInP p2 sigma
                                        v' = startEval (Omega iso (ValueT v)) -- Need to make sure the combination is fully reduced to normal form before evaluating
                                        in case v' of
                                            Evalue (Combination e1 e2) -> Evalue $ distributiveLetp sigma p (Combination e1 e2) e
                                            otherwise -> let sig2 = --debug("Pair: " ++ show p ++ "  Value:" ++ show v')
                                                                      catchMaybe errorString $ matching [] (productVal p) v'
                                                                        where errorString = "2-Failed to match LetE: " ++ show p ++ " = " ++ show v'
                                                         in --debug("V: " ++ show v ++ " V': " ++ show v' ++ " Sig2: " ++ show sig2)
                                                              reduceE (sig2++sigma) e
reduceE sigma (Val v) = --debug("Replacing v: " ++ show v ++ " with context: " ++ show sigma)
                          replaceV v sigma
reduceE sigma (Combination e1 e2)
  | AlphaVal a1 e' <- e1,
    a1 == 0 = (reduceE sigma e2) --Trimming the zeroes
  | AlphaVal a2 e' <- e2,
    a2 == 0 = (reduceE sigma e1)
  | otherwise = --debug("Combination...")
                  Evalue (Combination (Val(reduceE sigma e1)) (Val (reduceE sigma e2)))
reduceE sigma (AlphaVal 0 e) = Evalue $ AlphaVal 0 e --AS per algebraic rules, if alpha is 0 the expression is void, so we don't evaluate it
reduceE sigma (AlphaVal alpha e) = Evalue $ AlphaVal alpha $ Val $ reduceE sigma e
--reduceE sigma e = --debug("No evaluation for: " ++ show e)
--                    Evalue e


reduceLinearE :: Alpha -> Sigma -> E -> V
reduceLinearE 0 sig e = Evalue $ AlphaVal 0 (Val $ bottomValue e) -- Don't need to evaluate te expression if amplitude is zero.
reduceLinearE a sig e = reduceE sig e

isoReducing :: Iso -> Iso
isoReducing (App (Lambda f omega) (App omega2 omega3)) = case substitution [] f omega2 omega of
                                                            Nothing -> --debug("\nSubstitution failed:" ++ f ++ " for " ++ show omega2 ++ " in" ++ show omega)
                                                                        omega
                                                            Just subs -> --debug("\nSubstituted: " ++ show subs)
                                                                          isoReducing (App subs omega3)
isoReducing (App (Lambda f omega) omega2) = case substitution [] f omega2 omega of
                                                Nothing -> --debug("\nSubstitution failed:" ++ f ++ " for " ++ show omega2 ++ " in" ++ show omega)
                                                            omega --Should never happen?
                                                Just subs -> --debug("\nSubstituted: " ++ show subs)
                                                              subs
isoReducing (App (App iso1 iso2) iso3) = isoReducing (App (isoReducing (App iso1 iso2)) iso3)
-- Does the language allow applications such as (iso1 (iso2 iso3)), where iso1 and iso2 are both higher order isos?? Wasn't really clear
-- If so, need to modify this function to allow for proper reducing of these.
-- Current implementation stops reducing when all isoVars from iso1 have been substituted.
--isoReducing (App iso (App iso2 iso3)) = isoReducing (App iso $ isoReducing (App iso2 iso3))
--isoReducing ()
--isoReducing (App (Clauses c) iso2) = error "Hey!"
isoReducing iso = error $ "Cannot reduce: " ++ show iso




substitution :: [String] -> String -> Iso ->Iso -> Maybe Iso
substitution boundVars f omega2 (IsoVar f') = if f' == f && not (f `elem` boundVars)
                                              then Just omega2
                                              else Nothing
substitution boundVars f omega2 (Lambda g iso) = Just $ Lambda g $ testSubs iso $ substitution (g:boundVars) f omega2 iso
substitution boundVars f omega2 (App iso1 iso2) = Just $ App (testSubs iso1 $ substitution boundVars f omega2 iso1)
                                                    (testSubs iso2 $ substitution boundVars f omega2 iso2)
substitution boundVars f omega2 (Clauses listVe) = Just $ Clauses $ substitutionInClauses boundVars listVe f omega2
                                        -- The code for substituion on Apps is equivalent to this:
                                        -- let subs1 = substitution f omega2 iso1
                                        --     subs2 = substitution f omega2 iso2
                                        -- in case subs1 of
                                        --     Nothing -> case subs2 of
                                        --                   Nothing -> Just $ App iso1 iso2
                                        --                   Just s2 -> Just $ App iso1 s2
                                        --     Just s1 -> case subs2 of
                                        --                   Nothing -> Just $ App s1 iso2
                                        --                   Just s2 -> Just $ App s1 s2
substitution boundVars f omega2 (Fixpoint g iso) = Just $ Fixpoint g $ testSubs iso $ substitution (g:boundVars) f omega2 iso
--substitution f omega2 iso = --debug ("om2: " ++ show omega2 ++ "is: " ++ show iso)
  --                            Nothing

--Goes through the clauses, substituting isos found in LetExpressions. Returns the substituted clauseList
substitutionInClauses :: [String] -> [(V,E)] -> String -> Iso -> [(V,E)]
substitutionInClauses boundVars [] _ _ = []
substitutionInClauses boundVars (e:listE) f omega2 = (fst e, subIsoInLet boundVars (snd e) f omega2)
                                              : substitutionInClauses boundVars listE f omega2
--Substitutes isos in letExpressions if applicable, otherwise return the expression itself
subIsoInLet :: [String] -> E -> String -> Iso -> E
subIsoInLet boundVars (LetE p iso p2 e) f omega2 = LetE p (testSubs iso $ substitution boundVars f omega2 iso) p2 $ subIsoInLet boundVars e f omega2
subIsoInLet boundVars (Combination e1 e2) f omega2 = Combination (subIsoInLet boundVars e1 f omega2) (subIsoInLet boundVars e2 f omega2)
subIsoInLet boundVars (AlphaVal alpha e) f omega2 = AlphaVal alpha $ subIsoInLet boundVars e f omega2
subIsoInLet boundVars e _ _= e

--Checks if substitution has ocurred in an iso. If so, return the resulting substitution.
--If it hasn's, return the original iso
testSubs :: Iso -> Maybe Iso -> Iso
testSubs iso Nothing = iso
testSubs iso (Just s) = s

matchClauses :: [(V,E)] -> V -> Int-> (Sigma,Int)
matchClauses [] v i = ([],i)
-- matchClauses list (Evalue v) i = matchLinearCombinations list v i
matchClauses (ve:list) v i = let sig =  matching [] (fst ve) v
                              in case sig of
                                    Just sigma -> --debug("matched: " ++ show v ++ "sig:" ++ show sig)
                                                      (sigma,i)
                                    Nothing    -> --debug("Can't match pattern: " ++ show (fst ve) ++ " with value:" ++ show v)
                                                      matchClauses list v $ i+1

-- Applies pattern-matching to all values in a linear combination,
-- generating the sum Wi by combining the results. Original values amplitudes are joined with the resulting ones.
matchLinearCombinations :: [(V,E)] -> E -> Int -> Either [Char] V
matchLinearCombinations ve e i = let --e' = algebraicProperties e -- IF we are doing the tensor rep, there's no need to apply the properties here.
                                     tensorE = distributivePropExtended e -- For consistency. Will do nothing to a single qubit state, or a state already in tensor representation.
                                                                              -- This is important on representing a n-qubit state as <q1,<q2,...>>
                                                                              -- In order for a function application to succeed, all members of a tuple need to be pure values
                                     vlist = grabValuesFromCombinations tensorE --e'
                                     (alphas,vs) = listsFromPairs vlist
                                     sigmas = [matchClauses ve (v) 0 | v <- vs]
                                     in if checkSigmas sigmas (length ve) then
                                          let
                                            --wi' = --debug("List:: " ++ show vs)
                                              --      [reductionRules (Omega (Clauses ve) (ValueT v)) | v <- vs]
                                            wi = [reduceLinearE a (fst s) (snd $ ve !! (snd s)) | s <- sigmas | a <- alphas]
                                            summs = sumWi alphas wi
                                            result = Evalue $! algebraicProperties summs
                                            in Right result
                                        else error $ "Pattern-matching failed for valueSet: " ++ show vs ++ "  with sigmas: " ++ show sigmas

trimZeroes :: [V] -> [V]
trimZeroes [] = []
trimZeroes ((Evalue e1):vlist)
  | AlphaVal a e <- e1,
    a == (0:+0) = trimZeroes vlist
  | otherwise = (Evalue e1) : (trimZeroes vlist)
trimZeroes (e:vlist) = e : (trimZeroes vlist)


checkSigmas :: [(Sigma,Int)] -> Int -> Bool
checkSigmas [] _ = True
checkSigmas (s:sigmas) i = if i <= snd s then False
                            else checkSigmas sigmas i


sumWi :: [Alpha] -> [V] -> E
sumWi (a:[])( e : []) = case e of
                                  Evalue (Val (Evalue e2)) -> algebraicProperties $ AlphaVal a e2
                                  (Evalue e)        -> algebraicProperties $ AlphaVal a e
                                  otherwise         -> algebraicProperties $ AlphaVal a (Val e)
sumWi (a:alphas)( e: vlist) = case e of
                                        Evalue (Val (Evalue e2)) -> Combination e' (sumWi alphas vlist)
                                                                where e' = algebraicProperties $ AlphaVal a e2
                                        Evalue e                 -> Combination e' (sumWi alphas vlist)
                                                                where e' = algebraicProperties $ AlphaVal a e
                                        otherwise                -> Combination e' (sumWi alphas vlist)
                                                                where e' = algebraicProperties $ AlphaVal a (Val e)
sumWi as es = error $ "Cannot build sum of: " ++ show as ++ "  and: " ++ show es
--AlphaVal alpha (Comb alphatt alphaff)

--Extracts Alphas and Values from a linear Combination
grabValuesFromCombinations :: E -> [(Alpha,V)]
grabValuesFromCombinations (Combination e1 e2) = grabValuesFromCombinations e1 ++ grabValuesFromCombinations e2
grabValuesFromCombinations (AlphaVal a (Val v)) = [(a,v)]
grabValuesFromCombinations (Val v) = [((1:+0),v)]
grabValuesFromCombinations e = error $ "Couldn't extract value from: " ++ show e
-- grabValuesFromCombinations (AlphaVal a e) = [(a,v)] where v = grabValuesFromCombinations e

{- -}
fullyReduceAlgebra :: E -> E
fullyReduceAlgebra e = if combFullyReduced e then e
                       else fullyReduceAlgebra $ algebraicProperties e

--Implements the algebraic properties for linear combination.
--
algebraicProperties :: E -> E
algebraicProperties (AlphaVal a (Combination e1 e2)) = Combination e1' e2'
                                                        where e1' = algebraicProperties (AlphaVal a e1)
                                                              e2' = algebraicProperties (AlphaVal a e2)
algebraicProperties (AlphaVal a (AlphaVal b e)) = AlphaVal (a*b) e
algebraicProperties (AlphaVal a (Val (Evalue e))) = algebraicProperties (AlphaVal a e)
algebraicProperties (AlphaVal a (Val v))
  | a == (1:+0) = Val v
  | otherwise = AlphaVal a (Val v)
algebraicProperties (Combination (AlphaVal a e1) (AlphaVal b e2))
  | a == (0:+0) = algebraicProperties $ AlphaVal b e2
  | b == (0:+0) = algebraicProperties $ AlphaVal a e1
  | e1 == e2 = algebraicProperties $ AlphaVal (a+b) e1
  | otherwise = --debug("-,-")
                  (Combination (algebraicProperties $ AlphaVal a e1) (algebraicProperties $ AlphaVal b e2))
--algebraicProperties (Combination (AlphaVal a e1) e2) = Combination (algebraicProperties (AlphaVal a e1)) (algebraicProperties e2)
algebraicProperties (Combination e1 e2)
  = if combFullyReduced (Combination e1 e2)
      then debug("Reduced combination: " ++ show (Combination e1 e2))
            remakeCombination $ addAllCombinations $ pairAlphasWithValues True (Combination e1 e2)
    else case e1 of
           AlphaVal a (AlphaVal b e) -> algebraicProperties $ Combination (algebraicProperties e1) e2
           AlphaVal a (Combination e3 e4) -> algebraicProperties $ Combination (algebraicProperties e1) e2
           Combination e3 e4 -> if combFullyReduced (e1)
                                     then debug("Combination: e1 reduced " ++ show e1)
                                            algebraicProperties $ Combination e1 $ (algebraicProperties . distributivePropExtended) e2
                                 else debug("Combination2: e1 not done" ++ show e1)
                                        algebraicProperties $ Combination ((algebraicProperties . distributivePropExtended) e1) e2
           otherwise ->  case e2 of
                             AlphaVal a (AlphaVal b e) -> algebraicProperties $ Combination e1 (algebraicProperties e2)
                             AlphaVal a (Combination e3 e4) -> algebraicProperties $ Combination e1 (algebraicProperties e2)
                             Combination e3 e4 -> if combFullyReduced (e2)
                                                       then debug("Combination3: both reduced" ++ show e2)
                                                              algebraicProperties $ Combination e1 e2 -- Should never arise???
                                                   else debug("Combination4: e2 not done" ++ show e2)
                                                          algebraicProperties $ Combination e1 $ (algebraicProperties . distributivePropExtended) e2
                             otherwise ->  Combination e1 e2
  -- | AlphaVal a (Combination e3 e4) <- e1 = algebraicProperties $ Combination (algebraicProperties e1) e2
  -- | AlphaVal a (Combination e3 e4) <- e2 = algebraicProperties $ Combination e1 (algebraicProperties e2)
  -- | otherwise = remakeCombination $ addAllCombinations $ pairAlphasWithValues True (Combination e1 e2)

algebraicProperties (Val v)
  | Evalue e <- v = algebraicProperties e
  | otherwise = Val v
algebraicProperties e = error $ "Undefined AlgebraicProperties for: " ++ show e
                        --error $ "no can do: " ++ show e




addAllCombinations :: [(Alpha,E)] -> [(Alpha,E)]
addAllCombinations [] = []
addAllCombinations (a1:list) = let list' = adds a1 list
                               in if list' == list then a1 : addAllCombinations list
                                  else addAllCombinations list'



adds :: (Alpha, E) -> [(Alpha, E)]  -> [(Alpha, E)]
adds a1 [] = []
adds a1 (a2:list) = case addIfEqual a1 (a2) of
                         Just a -> (a:list)
                         Nothing -> (a2) : adds a1 list

addIfEqual :: (Alpha, E) -> (Alpha, E) -> Maybe (Alpha, E)
addIfEqual (a1,e1) (a2,e2) = if e1 == e2 then Just (a1+a2,e1)
                             else Nothing



--Takes a combination and creates a list pairing the amplitudes with their related values.
-- The bool argument is a flag indicating if zero amplitudes should be ignored.
pairAlphasWithValues :: Bool -> E -> [(Alpha, E)]
pairAlphasWithValues b (AlphaVal a e)
  | a == 0 && b = []
  | otherwise = (a,e) : []
pairAlphasWithValues b (Combination e1 e2) = pairAlphasWithValues b e1 ++ pairAlphasWithValues b e2
pairAlphasWithValues b (Val (Evalue e)) = pairAlphasWithValues b e --Casting a Value back to an ExtendedVal
pairAlphasWithValues b (Val v) = pairAlphasWithValues b (AlphaVal (1:+0) (Val v)) --
pairAlphasWithValues b e = error $ "Something went wrong (pairingAlphas): " ++ show e


--Remake the original combination (Combination e1 (Combination e2 e3)) after applying the algebraicProperties.
--Since (Comb e2 e3) has been tested, is impossible to get both combinations reduced to an AlphaVal at this point.
remakeCombination :: [(Alpha, E)] -> E
remakeCombination ((a,e):[]) = AlphaVal a e
remakeCombination ((a,e):list) = Combination (AlphaVal a e) $ remakeCombination list




productVal :: P -> V
productVal (EmptyP) = EmptyV
productVal (Xprod s) = Xval s
productVal (PairP p1 p2) = PairV (productVal p1) $ productVal p2

isVal:: Term -> Bool
isVal _ = True
-- reduction:: Term -> V
-- reduction (Let (PairP p1 p2) v1 t2) = replace t2 $ semantics [] p v1 --LetE


-- reduction2:: Iso -> V -> V
-- reduction2 (Clauses ve) v = case matchAll ve v of
--                               Left () -> error "No matching v"
--                               Right (sig,e) -> replace e sig
--
-- matchAll:: [(V,E)] -> V -> Either () (Sigma,E)
-- matchALl [] v = Left ()
-- matchAll (ve:list) v = case semantics [] (fst ve) v of
--                           []  -> matchAll (head list) v
--                           sig -> Right (sig,snd ve)
--
---------------------------------------------------------Program inversion
-- Not implemented yet
-- If we consider 2 well defined isos F and G, and valueTerm x, with program p being (F G) x, this function should allow the inversion of the whole ting.
-- For every program, inversion could be done by this function: p^-1 = (F G)^-1 ((F G )x)
invertTerm :: Term -> Term
invertTerm (Let p t1 t2) = Let p (invertTerm t1) (invertTerm t2)
invertTerm (Omega iso t1) = Omega (invertIso iso) (invertTerm t1)
invertTerm t = t

-------------------------------------- Iso Inversion


invertLinearClauses :: [V] -> [E] -> Int -> [(V,E)]
invertLinearClauses _ [] _ = []
invertLinearClauses v (e:elist) i = let (v',e') = swapCombinationVals v e i
                                        invE = invertExtendedValue e'
                                        in (v',invE): invertLinearClauses v elist (i+1)


swapCombinationVals :: [V] -> E -> Int -> (V,E)
swapCombinationVals vlist (Combination e1 e2) i = let e' =  pairAlphasWithValues False (Combination e1 e2)
                                                      swappedE =  swapVals vlist e'
                                                      v' = toValue $ snd $ e' !! i
                                                      in (v',remakeCombination swappedE)
swapCombinationVals vlist (LetE p1 iso p2 e') i = let (v',newE) = swapCombinationVals vlist e' i
                                                      in (v', LetE p1 iso p2 newE)
swapCombinationVals vlist (AlphaVal (1:+0) e) i = (toValue e, AlphaVal (1:+0) (Val $ head vlist)) -- For this to occur, iso must be defined as a single clause.

toValue :: E -> V
toValue (Val v) = v
toValue (AlphaVal a e) = toValue e
toValue _ = error "Should never occur in a well-typed expression"


swapVals :: [V] -> [(Alpha,E)] -> [(Alpha,E)]
swapVals [] [] = []
swapVals (v:vlist) ((a,e):aelist) = (a,Val v) : swapVals vlist aelist


invertCl :: [(V,E)] -> [(V,E)]
invertCl [] = []
invertCL list = let (values,linearEs) = listsFromPairs list
                    alphas = getLinearTerms linearEs
                    in if (oZ alphas)
                        then invertClauses list
                        else
                          let matrix = (fromLists . getLinearTerms) linearEs
                              inverseLinearAlphas = toLists $ wrap $ inverse matrix
                              inverseLinears = rebuildEs linearEs inverseLinearAlphas
                              newClauses = invertLinearClauses values inverseLinears 0
                              in newClauses
                      --error $ "NC: " ++ show newClauses

rebuildEs :: [E] -> [[Alpha]] -> [E]
rebuildEs [] [] = []
rebuildEs (e:elist) (alphas:alplist) = rebuild e alphas : rebuildEs elist alplist

rebuild :: E -> [Alpha] -> E
rebuild (Combination e1 e2) (alist) = remakeCombination a'e
                                        where a'e = swapAlphas alist $ pairAlphasWithValues False (Combination e1 e2)
rebuild (LetE p1 iso p2 e') (alist) = LetE p1 iso p2 $ rebuild e' alist
rebuild (AlphaVal (1:+0) e) (alist) = AlphaVal (1:+0) e
rebuild _ _ = error "Right-hand side of clauses Are neither a Combination nor a LetExpression"

swapAlphas :: [Alpha] -> [(Alpha,E)] -> [(Alpha,E)]
swapAlphas [] [] = []
swapAlphas (a':alist) ((a,e):aelist)  = (a',e) : swapAlphas alist aelist

invertType :: T -> T
invertType (Iso a b) = Iso b a
invertType (Comp a b t) = Comp b a (invertType t)

invertIso :: Iso -> Iso
invertIso (IsoVar f) = IsoVar $ f ++ "'"
invertIso (App omega1 omega2) = App (invertIso omega1) (invertIso omega2)
invertIso (Lambda f omega) = Lambda (f ++ "'") (invertIso omega)
invertIso (Fixpoint f omega) = Fixpoint (f ++ "'") (invertIso omega)
invertIso (Clauses listVE) = Clauses $ invertCL listVE


invertClauses :: [(V,E)] -> [(V,E)]
invertClauses [] = []
invertClauses (ve:listVE) = let e' = invertExtendedValue $ snd ve
                                v' = bottomValue $ snd ve
                            in buildInverted ve e' v' : invertClauses listVE

invertExtendedValue :: E -> E
invertExtendedValue (LetE p1 omega p2 e) = let omega' = invertIso omega in
                                               case invertExtendedValue e of
                                                (LetE p1' omega'' p2' e') -> ----debug("Inverted: " ++ (show $ LetE p1' omega'' p2' thisLet))
                                                                                swapBottom (LetE p1' omega'' p2' e') thisLet
                                                                               --LetE p1' omega'' p2' thisLet
                                                      where thisLet = LetE p2 omega' p1 e'
                                                otherwise -> ----debug("Inverted: " ++ (show $ LetE p2 omega' p1 $ invertExtendedValue e))
                                                              LetE p2 omega' p1 $ invertExtendedValue e
invertExtendedValue e = e

swapBottom :: E -> E -> E
swapBottom (LetE p1 omega p2 e) (LetE pp omegap pp2 e2)
  | LetE p1' omega' p2' e' <- e = LetE p1 omega p2 $ swapBottom e (LetE pp omegap pp2 e2)
  | otherwise = LetE p1 omega p2 (LetE pp omegap pp2 e)

changeBottomVal :: E -> V -> E
changeBottomVal (LetE p1 omega p2 e) v
  | LetE p1' omega' p2' e' <- e = LetE p1 omega p2 $ changeBottomVal e v
  | otherwise = LetE p1 omega p2 (Val v)
changeBottomVal (Val v') v = Val v
changeBottomVal e v = Val v -- Should not find combinations and alphas here.

buildInverted :: (V,E) -> E -> V -> (V,E)
buildInverted ve (LetE p1 omega p2 e) v' = (v', changeBottomVal (LetE p1 omega p2 e) (fst ve))
buildInverted (v,e) e' v' = (v',Val v)
--buildInverted ve (e) v' = error $ "Cant build inverted:: " ++ show ve ++ " e: "++ show e ++ " v'" ++ show v'
