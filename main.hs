module Main where

import Quantum
import Data.Complex
--Testing case for parametrized conditional.
test1 :: String
test1 = let x = Xval "x"
            xP = Xprod "x"
            y = Xval "y"
            v1 = PairV (InjL EmptyV) x
            v2 = PairV (InjR EmptyV) x
            p1 = PairV (InjL EmptyV) y
            p2 = PairV (InjR EmptyV) y
            pterm = PairTerm (InjRt EmptyTerm) (XTerm "x")
            g = IsoVar "g"
            h = IsoVar "h"
            e1 = LetE (Xprod "y") g (Xprod "x")
                        (Combination (AlphaVal (1:+0) (Val p1)) (AlphaVal (0:+0) (Val p2)))
            e2 = LetE (Xprod "y") h (Xprod "x")
                        (Combination (AlphaVal (0:+0) (Val p1)) (AlphaVal (1:+0) (Val p2)))
            iso1 = Clauses [(v1,e1),(v2,e2)]
            lambdaH = Lambda "h" iso1
            lambdaG = Lambda "g" lambdaH
            bool = Sum One One
            a = One
            b = One
            boolXa = Prod bool a
            boolXb = Prod bool b
            isoAb = (Iso a b)
            t2 = Iso boolXa boolXb
            isoT1 = Comp a b t2
            isoType = Comp a b isoT1
            delta = [("x",One)]
            psi = []
            in ("Type:" ++ show (typeCheck delta psi lambdaG isoType) )
              --    ++ ("\nPairType:" ++ show (mytermTypeCheck delta psi pterm (Sum bool One)))

testMap :: String
testMap =
  let a = TypeVar 'a'
      b = TypeVar 'b'
      aB = Iso a b
      x = Xval "x"
      y = Xval "y"
      h = Xval "h"
      t = Xval "t"
      recursiveA = Rec a
      recursiveB = Rec b
      emptyList = InjL EmptyV
      l1 = PairV t emptyList
      l2 = InjR (PairV h l1)
      e1 = Val emptyList
      f = IsoVar "f"
      g = IsoVar "g"
      eE = LetE (Xprod "y") f (Xprod "t") (Val (InjR $ PairV x y))
      e2 = LetE (Xprod "x") g (Xprod "h") eE
      func = Clauses [(emptyList,e1),(l2,e2)]
      fixPf = Fixpoint "f" func
      lamG = Lambda "g" fixPf
      funType = Iso recursiveA recursiveB
      isoType = Comp a b funType
      delta = [("h",a),("t",recursiveA)]
      psi = []
      in ("Type2: " ++ show (typeCheck delta psi lamG isoType))


main = putStr test1
