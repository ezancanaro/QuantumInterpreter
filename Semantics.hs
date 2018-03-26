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
                                                                                    [] -> Just $ sigma1 `union` sigma2
                                                                                    otherwise -> Nothing
                                                  _ -> Nothing
matching _ term val = Nothing



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
reductionRules (Let p (ValueT v1) t2) = replace t2 $ catchMaybe $ matching  [] (productVal p) v1
reductionRules (Omega (Clauses isoDefs) (ValueT (Evalue e))) = wrap $ matchLinearCombinations isoDefs e 1
reductionRules (Omega (Clauses isoDefs) (ValueT v)) = let match = matchClauses isoDefs v 0 -- NOT COMPLETED YET
                                                          i = snd match
                                                          term = debug ("i: " ++ show i ++ "lista: " ++ show (length isoDefs))
                                                                    snd $ isoDefs !! i
                                                          in debug("Chosen:  "++ show (fst match) ++ " to: " ++ show term)
                                                              reduceE (fst match) term
                                      --Iso application: In case iso1 is a lambda, substitute the free-vars for iso2 and then apply term to it
reductionRules (Omega (App i1 i2) t) = reductionRules (Omega (isoReducing (App i1 i2)) t)
reductionRules (Omega (Fixpoint f (Clauses isoDefs)) (ValueT v)) = let unfoldedRecursion = debug ("My Val: " ++ show v)
                                                                                              buildLamFromFix f v (Clauses isoDefs)
                                                                       in reductionRules (Omega unfoldedRecursion (ValueT v))

--                                                                        i = snd match
--                                                                        term = debug ("i: " ++ show i ++ "lista: " ++ show (length isoDefs))
--                                                                                  snd $ isoDefs !! i
--                                                                        in debug("Chosen:  "++ show (fst match) ++ " to: " ++ show term)
--                                                                           if checkIfFixedPoint term f then reduceE (fst match) term
--                                                                           else reductionRules (Omega (isoReducing (Fixpoint f (Clauses isoDefs))) (ValueV t))
--                                                                                     --not correct

buildLamFromFix :: String -> V -> Iso -> Iso
buildLamFromFix f v fix = let listLams = findFixedPoint f 0 v fix
                              fix' = renameInFixedPoint f 0 fix
                              fixedNameIsoPairs = findFixedPoint f 0 v fix
                              (names,isos) = listsFromPairs fixedNameIsoPairs
                              lambdaChain = lambdaBuilding names fix'
                              appChain = debug ("Lams: " ++ show lambdaChain ++ "\n------------\n")
                                            appBuilding (reverse isos) lambdaChain
                              in debug ("::: " ++ show appChain ++ "\n------------\n")
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
                                           in debug ("fix': " ++ show fix' ++ " || pair: " ++ show pairNameIso ++ "\n------------\n")
                                                [pairNameIso] -- error ("EmptyV")
findFixedPoint f i (PairV list _) fix = let fix' = renameInFixedPoint f (i+1) fix
                                            pairNameIso = ((f ++ show i), renameIsoVars i fix')
                                            in debug ("fix': " ++ show fix' ++ " || pair: " ++ show pairNameIso ++ "\n------------\n")
                                                [pairNameIso] -- error ("PAIRV")
--Case of a list with elements -- Need to keep unfolding the iso.
findFixedPoint f i (InjR (PairV h t)) fix = let fix' = renameInFixedPoint f (i+1) fix
                                                pairNameIso = ((f ++ show i), renameIsoVars i fix')
                                                in debug ("fix': " ++ show fix' ++ " || pair: " ++ show pairNameIso ++ "\n------------\n")
                                                    pairNameIso : findFixedPoint f (i+1) t fix


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

--

--
--
-- checkIfFixedPoint :: E -> String -> Bool
-- checkIfFixedPoint (Val v) _ = True
-- checkIfFixedPoint (LetE p (IsoVar g) p2 e) f = if g==f then False
--                                                else checkIfFixedPoint e f
-- checkIfFixedPoint (Combination e1 e2) f = (checkIfFixedPoint e1 f) && checkIfFixedPoint e2 f
-- checkIfFixedPoint (AlphaVal alpha e) f = checkIfFixedPoint e f
replace::  Term -> Sigma -> V
replace (EmptyTerm) sig= EmptyV
replace (XTerm x) sig  = case lookup (x) sig of
                          Nothing -> error "Did not find Variable" --This is wrong!
                          Just v -> v
replace (InjLt v) sig  = InjL $ replace v sig
replace (InjRt v) sig  = InjR $ replace v sig
replace (PairTerm v1 v2) sig  = PairV (replace v1 sig) (replace v2 sig)


replaceV:: V -> Sigma ->V
replaceV (Xval x) sig = case lookup (x) sig of
                          Nothing -> error "Did not find Variable" --This is wrong!
                          Just v -> debug ("Value: " ++ show v ++ "\n------------\n")
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


reduceE :: Sigma -> E -> V
reduceE sigma (LetE p iso p2 e) = let   v = replaceInP p2 sigma
                                        v' = applicativeContext (Omega iso (ValueT v))
                                        sig2 = catchMaybe $ matching sigma (productVal p) v'
                                  in debug("V: " ++ show v ++ " V': " ++ show v' ++ " Sig2: " ++ show sig2)
                                      reduceE sig2 e
reduceE sigma (Val v) = debug("Replacing v: " ++ show v ++ " with context: " ++ show sigma)
                          replaceV v sigma
reduceE sigma (Combination e1 e2) = debug("Combination...")
                                     Evalue (Combination (Val(reduceE sigma e1)) (Val (reduceE sigma e2)))
reduceE sigma (AlphaVal alpha e) = Evalue $ AlphaVal alpha $ Val $ reduceE sigma e
--reduceE sigma e = debug("No evaluation for: " ++ show e)
--                    Evalue e

isoReducing :: Iso -> Iso
isoReducing (App (Lambda f omega) (App omega2 omega3)) = case substitution f omega2 omega of
                                                            Nothing -> debug("\nSubstitution failed:" ++ f ++ " for " ++ show omega2 ++ " in" ++ show omega)
                                                                        omega
                                                            Just subs -> debug("\nSubstituted: " ++ show subs)
                                                                          isoReducing (App subs omega3)
isoReducing (App (Lambda f omega) omega2) = case substitution f omega2 omega of
                                                Nothing -> debug("\nSubstitution failed:" ++ f ++ " for " ++ show omega2 ++ " in" ++ show omega)
                                                            omega --Should never happen?
                                                Just subs -> debug("\nSubstituted: " ++ show subs)
                                                              subs
isoReducing (App (App iso1 iso2) iso3) = isoReducing (App (isoReducing (App iso1 iso2)) iso3)
isoReducing iso = error $ "Cannot reduce: " ++ show iso


substitution :: String -> Iso ->Iso -> Maybe Iso
substitution f omega2 (IsoVar f') = if f' == f then Just omega2
                                    else Nothing
substitution f omega2 (Lambda g iso) = Just $ Lambda g $ testSubs iso $ substitution f omega2 iso --Need to check if f is freeVariable?

substitution f omega2 (App iso1 iso2) = Just $ App (testSubs iso1 $ substitution f omega2 iso1)
                                                    (testSubs iso2 $ substitution f omega2 iso2)
substitution f omega2 (Clauses listVe) = Just $ Clauses $ substitutionInClauses listVe f omega2
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
substitution f omega2 (Fixpoint g iso) = Just $ Fixpoint g $ testSubs iso $ substitution f omega2 iso
--substitution f omega2 iso = debug ("om2: " ++ show omega2 ++ "is: " ++ show iso)
  --                            Nothing

--Goes through the clauses, substituting isos found in LetExpressions. Returns the substituted clauseList
substitutionInClauses :: [(V,E)] -> String -> Iso -> [(V,E)]
substitutionInClauses [] _ _ = []
substitutionInClauses (e:listE) f omega2 = (fst e, subIsoInLet (snd e) f omega2)
                                              : substitutionInClauses listE f omega2
--Substitutes isos in letExpressions if applicable, otherwise return the expression itself
subIsoInLet :: E -> String -> Iso -> E
subIsoInLet (LetE p iso p2 e) f omega2 = LetE p (testSubs iso $ substitution f omega2 iso) p2 $ subIsoInLet e f omega2
subIsoInLet (Combination e1 e2) f omega2 = Combination (subIsoInLet e1 f omega2) (subIsoInLet e2 f omega2)
subIsoInLet (AlphaVal alpha e) f omega2 = AlphaVal alpha $ subIsoInLet e f omega2
subIsoInLet e _ _= e

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
                                    Just sigma -> debug("matched: " ++ show v ++ "sig:" ++ show sig)
                                                      (sigma,i)
                                    Nothing    -> debug("Can't match pattern: " ++ show (fst ve) ++ " with value:" ++ show v)
                                                      matchClauses list v $ i+1


matchLinearCombinations :: [(V,E)] -> E -> Int -> Either [Char] V
matchLinearCombinations ve e i = let e' = algebraicProperties e
                                     vlist = grabValuesFromCombinations e'
                                     (alphas,vs) = listsFromPairs vlist
                                     sigmas = [matchClauses ve (v) 0 | v <- vs]
                                     wi = [reduceE (fst s) (snd $ ve !! (snd s)) | s <- sigmas]
                                     summs = sumWi alphas wi
                                     result = Evalue $! algebraicProperties summs
                                     in Right result

sumWi :: [Alpha] -> [V] -> E
sumWi (a:[])( (Evalue e): []) = case e of
                                  (Val (Evalue e2)) -> algebraicProperties $ AlphaVal a e2
                                  otherwise         -> algebraicProperties $ AlphaVal a e
sumWi (a:alphas)( (Evalue e): vlist) = case e of
                                        (Val (Evalue e2)) -> Combination e' (sumWi alphas vlist)
                                                                where e' = algebraicProperties $ AlphaVal a e2
                                        otherwise         -> Combination e' (sumWi alphas vlist)
                                                                where e' = algebraicProperties $ AlphaVal a e

--AlphaVal alpha (Comb alphatt alphaff)


grabValuesFromCombinations :: E -> [(Alpha,V)]
grabValuesFromCombinations (Combination e1 e2) = grabValuesFromCombinations e1 ++ grabValuesFromCombinations e2
grabValuesFromCombinations (AlphaVal a (Val v)) = [(a,v)]
-- grabValuesFromCombinations (AlphaVal a e) = [(a,v)] where v = grabValuesFromCombinations e


algebraicProperties :: E -> E
algebraicProperties (AlphaVal a (Combination e1 e2)) = Combination e1' e2'
                                                        where e1' = algebraicProperties (AlphaVal a e1)
                                                              e2' = algebraicProperties (AlphaVal a e2)
algebraicProperties (AlphaVal a (AlphaVal b e)) = AlphaVal (a*b) e
algebraicProperties (AlphaVal a (Val (Evalue e))) = algebraicProperties (AlphaVal a e)
algebraicProperties (Combination (AlphaVal a e1) (AlphaVal b e2))
  | e1 == e2 = AlphaVal (a+b) e1
  | otherwise = (Combination (AlphaVal a e1) (AlphaVal b e2))
algebraicProperties (Combination e1 e2) = let e' = pairAlphasWithValues (Combination e1 e2)
                                            in remakeCombination $ addAllCombinations e'
algebraicProperties e = error "...."
                        --error $ "no can do: " ++ show e

--Combination (a tt) (Combination a ff (combination a tt (Combination b ff)))


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

pairAlphasWithValues :: E -> [(Alpha, E)]
pairAlphasWithValues (AlphaVal a e) = (a,e) : []
pairAlphasWithValues (Combination e1 e2) = pairAlphasWithValues e1 ++ pairAlphasWithValues e2



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

-------------------------------------- Iso Inversion

invertType :: T -> T
invertType (Iso a b) = Iso b a
invertType (Comp a b t) = Comp b a (invertType t)

invertIso :: Iso -> Iso
invertIso (IsoVar f) = IsoVar $ f ++ "'"
invertIso (App omega1 omega2) = App (invertIso omega1) (invertIso omega1)
invertIso (Lambda f omega) = Lambda f (invertIso omega)
invertIso (Fixpoint f omega) = Fixpoint f (invertIso omega)
invertIso (Clauses listVE) = Clauses $ invertClauses listVE


invertClauses :: [(V,E)] -> [(V,E)]
invertClauses [] = []
invertClauses (ve:listVE) = let e' = invertExtendedValue $ snd ve
                                v' = bottomValue $ snd ve
                            in buildInverted ve e' v' : invertClauses listVE

invertExtendedValue :: E -> E
invertExtendedValue (LetE p1 omega p2 e) = LetE p2 (invertIso omega) p1 (invertExtendedValue e)
invertExtendedValue e = e

buildInverted :: (V,E) -> E -> V -> (V,E)
buildInverted ve (LetE p1 omega p2 e) v' = (v', (LetE p1 omega p2 $ Val $ fst ve))
