module Utils where
import AbstractData
import Debug.Trace

--Debugging flag-
doDebug = False
          --True
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
a = TypeVar 'a'
recursiveA = Rec a
b = TypeVar 'b'
recursiveB = Rec b
recBool = Rec bool
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
