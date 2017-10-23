module Main where

import Quantum

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
            e1 = LetE (Xprod "y") g (Xprod "x") (Val p1)
            e2 = LetE (Xprod "y") h (Xprod "x") (Val p2)
            iso1 = Pattern [(v1,e1),(v2,e2)]
            lambdaH = Lambda "h" iso1
            lambdaG = Lambda "g" lambdaH
            bool = Sum One One
            boolXb = Prod bool One
            t1 = bool
            t2 = Iso bool bool
            isoT1 = Comp bool bool t2
            isoType = Comp bool bool isoT1
            delta = [("x",One)]
            psi = []
            --Not working properly yet- Haven't implemented typeChecking for ExtendedValues
            in ("Type:" ++ show (typeCheck delta psi lambdaG isoType) )
              --    ++ ("\nPairType:" ++ show (mytermTypeCheck delta psi pterm (Sum bool One)))

main = putStr test1
