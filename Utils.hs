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
-----------------------------------------------


listsFromPairs :: [(a,b)] -> ([a],[b])
listsFromPairs listAB = (fmap fst listAB, fmap snd listAB)

--Function used to wrap evaluations of functions tha may raise a typing error.
--Used to avoid creating multiple conditionals on the function definitions. Needs a better name!!!
wrap :: Show b => Either b a -> a
wrap (Left err) = error (show err)
wrap (Right val) = val

catchMaybe :: Maybe a -> a
catchMaybe (Just something) = something
catchMaybe Nothing = error "Something failed"

--Returns the bottom value from an Extended Value. (Val(e))
bottomValue :: E -> V
bottomValue (Val v) = v
bottomValue (LetE p1 iso p2 e) = bottomValue e
bottomValue (Combination e1 e2) = bottomValue e1
bottomValue (AlphaVal alpha e) = bottomValue e

boolLists :: [Bool] -> Term
boolLists [] = InjLt EmptyTerm
boolLists (False:lb) = InjRt $ PairTerm (falseTerm) (boolLists lb)
boolLists (True:lb) = InjRt $ PairTerm (trueTerm) (boolLists lb)

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
