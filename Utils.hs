module Utils where
import AbstractData
import Debug.Trace
import Data.Complex
import Data.Number.CReal

--Debugging flag-
doDebug = False
          --True -- You honestly should not do it. Especially if you test a recursive function. It's legit madness. Believe me. And the voices.


--Making debug statements easier to use
debug a b = if doDebug then Debug.Trace.trace a b else b
--Remember to remove debugging statements after checks

-- Commonly used definitions of terms in the Abstract Syntax
bool = Sum One One --bool syntatic sugar
tt = InjL EmptyV -- true value
ff = InjR EmptyV -- false vaue
trueTerm = InjLt EmptyTerm --boolean terms
falseTerm = InjRt EmptyTerm
ttE = Val tt --boolean extended values
ffE = Val ff
xE = Val (Xval "x")
a = TypeVar 'a'
recursiveA = Rec a
b = TypeVar 'b'
recursiveB = Rec b
recBool = Rec bool
a1 = (1/sqrt(2)) :: CReal
a2 = (-1/sqrt(2)) :: CReal--fixed precision numbers
alpha = (a1 :+ 0)
beta = (a2 :+ 0) -- complex numbers
plusS = Combination (AlphaVal alpha ttE) (AlphaVal alpha ffE)
minusS =   Combination (AlphaVal alpha ttE) (AlphaVal beta ffE)
-----------------------------------------------
boolLists :: [Bool] -> Term
boolLists [] = InjLt EmptyTerm
boolLists (False:lb) = InjRt $ PairTerm (falseTerm) (boolLists lb)
boolLists (True:lb) = InjRt $ PairTerm (trueTerm) (boolLists lb)

langBool :: Int -> V
langBool 0 = tt
langBool 1 = ff

langBoolT :: Int -> Term
langBoolT 0 = ValueT tt
langBoolT 1 = ValueT ff

intRep :: [Int] -> V
intRep (x:y:[]) = PairV (langBool x) (langBool y)
intRep (x:list) = PairV (langBool x) (intRep list)

intRepT :: [Int] -> Term
intRepT (x:y:[]) = PairTerm (langBoolT x) (langBoolT y)
intRepT (x:list) = PairTerm (langBoolT x) (intRepT list)

dec2bin :: Int -> [Int] -- Pulled from: https://www.reddit.com/r/haskell/comments/1ikrzo/my_first_program_a_decimal_to_binary_converter/cb5g9md/
dec2bin = reverse . dec2bin'
  where dec2bin' 0 = []
        dec2bin' x = (x `mod` 2) : dec2bin' (x `quot` 2)

build2BytesInt :: Int -> Char -> Either V Term
build2BytesInt n 'v' = if length (dec2bin n) <= 16
                          then Left $ intRep $ replicate (16 - lX) 0 ++ l
                          else error $ "Only defined 2bytes ints for now."
                          where l = dec2bin n
                                lX = length l
build2BytesInt n 't' = if length (dec2bin n) <= 16
                          then Right $ intRepT $ replicate (16 - lX) 0 ++ l
                          else error $ "Only defined 2bytes ints for now."
                          where l = dec2bin n
                                lX = length l

-- Converts an int to a list of 0,1 and fills it with 0 on the left up to 'size' elements.
-- Returns a value or term representing the int as a tuple of boolean values.
buildInt :: Int -> Int -> Char -> Either V Term
buildInt n size 'v' = if length (dec2bin n) <= size
                          then Left $ intRep $ replicate (size - lX) 0 ++ l
                          else error $ "Cannot represent " ++show  n ++ ", with " ++ show size ++ " bits."
                          where l = dec2bin n
                                lX = length l
buildInt n size 't' = if length (dec2bin n) <= size
                          then Right $ intRepT $ replicate (size - lX) 0 ++ l
                          else error $ "Cannot represent " ++show  n ++ ", with " ++ show size ++ " bits."
                          where l = dec2bin n
                                lX = length l

listsFromPairs :: [(a,b)] -> ([a],[b])
listsFromPairs listAB = (fmap fst listAB, fmap snd listAB)

--Function used to wrap evaluations of functions tha may raise a typing error.
--Used to avoid creating multiple conditionals on the function definitions. Needs a better name!!!
wrap :: Show b => Either b a -> a
wrap (Left err) = error (show err)
wrap (Right val) = val

catchMaybe :: Maybe a -> a
catchMaybe (Just something) = something
catchMaybe Nothing = error "Failure on a Maybe returning function" -- Not really descriptive of the error, I know.
                                                    --Should update it to take an extra argument that can help identify the error.

--Returns the bottom value from an Extended Value. (Val(e))
bottomValue :: E -> V
bottomValue (Val v) = v
bottomValue (LetE p1 iso p2 e) = bottomValue e
bottomValue (Combination e1 e2) = bottomValue e1
bottomValue (AlphaVal alpha e) = bottomValue e


-- Function used to make sure all tuples of qubits are represented the same on the examples.
-- Not used directly by the interpreter, since I'm not sure if there's a semantic reason to differentiate (PairV (Pair v1 v2) v3) from (PairV v1 (PairV v2 v3)) in the whole language.
normalizeTuple :: V -> V
normalizeTuple (PairV (PairV v1 v2) v3) = PairV v1 (normalizeTuple (PairV v2 v3))
normalizeTuple (PairV v1 v2) = PairV v1 v2


fl:: Either a b -> a
fl (Left x) = x

fr:: Either a b -> b
fr (Right x) = x

grabPatternTypesFromAnnotation :: (Iso,T) -> Delta
grabPatternTypesFromAnnotation (Clauses isoDefs, (Iso a _)) = let (pats,_) = listsFromPairs isoDefs
                                                                in concat $ map (matchPatternWithAnnotation a) pats
grabPatternTypesFromAnnotation (Lambda _ iso, (Comp _ _ t)) = grabPatternTypesFromAnnotation (iso,t)
grabPatternTypesFromAnnotation (Fixpoint _ iso,t) = grabPatternTypesFromAnnotation (iso,t)

matchPatternWithAnnotation :: A -> V -> Delta
matchPatternWithAnnotation _ (EmptyV) = []
matchPatternWithAnnotation a (Xval s)  = (s,a):[]
matchPatternWithAnnotation (Sum a b) (InjL v)  = matchPatternWithAnnotation a v
matchPatternWithAnnotation (Sum a b) (InjR v)  = matchPatternWithAnnotation b v
matchPatternWithAnnotation (Prod a b) (PairV v1 v2) = matchPatternWithAnnotation a v1 ++ matchPatternWithAnnotation b v2
matchPatternWithAnnotation (Rec a) (InjR (PairV v1 v2)) = matchPatternWithAnnotation a v1 ++ matchPatternWithAnnotation (Rec a) v2
matchPatternWithAnnotation (Rec a) (InjL EmptyV) = []
matchPatternWithAnnotation a v = error $ "Cannot associate value: " ++ show v ++ "with type annotation: " ++ show a

getLinearAlphas :: E -> [Alpha]
getLinearAlphas (Combination (AlphaVal a v1) v2) = a : getLinearAlphas v2
getLinearAlphas (Combination (Val v) v2) = (1 :+ 0) : getLinearAlphas v2 -- 1*CVal = CVal
getLinearAlphas (Val v) = (1 :+ 0):[]
getLinearAlphas (AlphaVal a _) = a:[]
getLinearAlphas (LetE _ _ _ e) = getLinearAlphas e

-- getLinearTerms :: [E] ->[[Alpha]]
-- getLinearTerms [] = []
-- getLinearTerms (e:elist) = getLinearAlphas e : getLinearTerms elist

getLinearTerms :: [E] ->[[Alpha]]
getLinearTerms (elist) = map getLinearAlphas elist
