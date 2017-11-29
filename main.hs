module Main where

import Quantum
import Data.Complex
import Numeric.Fixed
import Control.Monad
import System.Exit



hadIso :: Iso
hadIso = let  tt = InjL EmptyV
              ff = InjR EmptyV
              a1 = toFixed (1/sqrt(2))
              a2 = toFixed (-1/sqrt(2))
              alpha = (a1 :+ 0)
              beta = ( a2 :+ 0)
              eTT = Val tt
              eFF = Val ff
              e1 = Combination (AlphaVal alpha eTT) (AlphaVal alpha eFF)
              e2 = Combination (AlphaVal alpha eTT) (AlphaVal beta eFF)
              had = Clauses [(tt,e1),(ff,e2)]
              bool = Sum One One
              isoType = Iso bool bool
              delta = []
              psi = []
              check = Omega had (InjLt EmptyTerm)
              in had


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
                        (Combination (AlphaVal (0:+0) (Val p1)) (AlphaVal ((-1):+0) (Val p2)))
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
            had = hadIso
            check = Omega (App lambdaG (App had had)) (PairTerm (InjLt EmptyTerm) EmptyTerm)
            in ("If Type:" ++ show (typeCheck delta psi lambdaG isoType) )
              ++ "\nEvals to:\n\t" ++ show (applicativeContext check)
              --    ++ ("\nPairType:" ++ show (mytermTypeCheck delta psi pterm (Sum bool One)))

testMap :: String
testMap =
  let a = TypeVar 'a'
      b = TypeVar 'b'

      x = Xval "x"
      y = Xval "y"
      h = Xval "h"
      t = Xval "t"
      recursiveA = Rec a
      recursiveB = Rec b
      emptyList = InjL EmptyV
      l1 = InjR (PairV emptyList emptyList)
      l2 = InjR (PairV h t)
      e1 = (Combination (Val emptyList) (AlphaVal (0:+0) (Val emptyList)))
      f = IsoVar "f"
      g = IsoVar "g"
      eE = LetE (Xprod "y") f (Xprod "t")
              (Combination (AlphaVal (0:+0) (Val (InjR $ PairV x y))) (Val (InjR $ PairV x y)))
      e2 = LetE (Xprod "x") g (Xprod "h") eE
      func = Clauses [(emptyList,e1),(l2,e2)]
      fixPf = Fixpoint "f" func
      lamG = Lambda "g" fixPf
      funType = Iso recursiveA recursiveB
      isoType = Comp a b funType
      delta = [("h",a),("t",recursiveA)]
      psi = []
      had = hadIso
      check = Omega (App lamG had) (InjLt EmptyTerm)
      in ("Map Type: " ++ show (typeCheck delta psi lamG isoType))
      --  ++  "\n\nEvals to:\n\t " ++ show (applicativeContext check)

testHad :: String
testHad = let tt = InjL EmptyV
              ff = InjR EmptyV
              a1 = toFixed (1/sqrt(2))
              a2 = toFixed (-1/sqrt(2))
              alpha = (a1 :+ 0)
              beta = ( a2 :+ 0)
              eTT = Val tt
              eFF = Val ff
              e1 = Combination (AlphaVal alpha eTT) (AlphaVal alpha eFF)
              e2 = Combination (AlphaVal alpha eTT) (AlphaVal beta eFF)
              had = Clauses [(tt,e1),(ff,e2)]
              bool = Sum One One
              isoType = Iso bool bool
              delta = []
              psi = []
              check = Omega had (InjLt EmptyTerm)
              in ("Had Type:" ++ show (typeCheck delta psi had isoType) )
                ++  "\n\nEvals to:\n\t " ++ show (applicativeContext check)

testMapAcc :: String
testMapAcc =  let a = TypeVar 'a'
                  b = TypeVar 'b'
                  c = TypeVar 'c'
                  x = Xval "x"
                  y = Xval "y"
                  h = Xval "h"
                  t = Xval "t"
                  z = Xval "z"
                  h' = Xval "h'"
                  t' = Xval "t'"
                  recursiveC = Rec c
                  recursiveB = Rec b
                  emptyList = InjL EmptyV
                  xEmpty = PairV x emptyList
                  tl = PairV t emptyList
                  ht = InjR (PairV h t)
                  xHT = PairV x ht

                  yh' = PairP (Xprod "y") (Xprod "h'")
                  xh = PairP (Xprod "x") (Xprod "h")
                  yt = PairP (Xprod "y") (Xprod "t")
                  zt' = PairP (Xprod "z") (Xprod "t'")

                  tl' = PairV t' emptyList
                  h't' = InjR (PairV h' t')
                  zh't' = Val (PairV z h't')

                  let1E = Combination (AlphaVal (0:+0) zh't') zh't'

                  f = IsoVar "f"
                  g = IsoVar "g"
                  let1 = LetE zt' f yt let1E
                  let2 = LetE yh' g xh let1
                  e1 = Combination (Val xEmpty) (AlphaVal (0:+0) (Val xEmpty))
                  e2 = let2

                  func = Clauses [(xEmpty,e1),(xHT,e2)]
                  fixPf = Fixpoint "f" func
                  lamG = Lambda "g" fixPf

                  aXb = Prod a b
                  aXc = Prod a c
                  aXrecB = Prod a recursiveB
                  aXrecC = Prod a recursiveC
                  gType = Iso aXb aXc
                  funType = Iso aXrecB aXrecC

                  isoType = Comp aXb aXc funType
                  delta = [("x",a),("h",b),("t",recursiveB)]
                  psi = []
                  in ("MapAcc Type: " ++ show (typeCheck delta psi lamG isoType))

testCnot :: String
testCnot = let  bool = Sum One One
                recBool = Rec bool
                recBoolXbool = Prod recBool bool
                emptyList = InjL EmptyV
                tb = Xval "tb"
                cbs = Xval "cbs"
                ff = InjR EmptyV
                tt = InjL EmptyV
                tb' = Xprod "tb'"
                tb'v = Xval "tb'"
                cbs' = Xprod "cbs'"
                noT = IsoVar "not"
                emptyTb = PairV emptyList tb
                emptyTb' = Val (PairV emptyList (Xval "tb'"))
                ffCBS = InjR (PairV ff cbs)
                ttCBS = InjR (PairV tt cbs)
                ffCBStb = PairV ffCBS tb
                ttCBStb = PairV ttCBS tb
                cbs'tb' = PairP cbs' tb'
                cbstb = PairP (Xprod "cbs") (Xprod "tb")
                ttCBS' = InjR (PairV tt (Xval "cbs'"))
                ttCBS'tb' = PairV ttCBS' (Xval "tb'")
                f = IsoVar "f"

                comb1' = Combination (AlphaVal (0:+0) (Val emptyTb)) (AlphaVal (0:+0) (Val emptyTb))
                comb2' = Combination (Val ffCBStb) (AlphaVal (0:+0) (Val ffCBStb))
                comb3' = Combination (AlphaVal (0:+0) (Val ttCBS'tb')) (Val ttCBS'tb')
                comb1 = Combination (Val emptyTb) comb1'
                comb2 = Combination (AlphaVal (0:+0) (Val ffCBStb)) comb2'
                comb3 = Combination (AlphaVal (0:+0) (Val ttCBS'tb')) comb3'

                let1 = LetE tb' noT (Xprod "tb") comb1
                extV = comb2
                let2 = LetE cbs'tb' f cbstb comb3

                fun = Clauses [(emptyTb,let1),(ffCBStb,extV),(ttCBStb,let2)]
                cnot = Fixpoint "f" fun

                isoType = Iso recBoolXbool recBoolXbool
                delta = [("tb",bool),("cbs",recBool)]
                psi = [("not",Iso bool bool)]

                in ("Cnot Type: " ++ show (typeCheck delta psi cnot isoType))

testTerms :: String
testTerms = let  bool = Sum One One
                 empty = EmptyTerm
                 x = XTerm "x"
                 y = XTerm "y"
                 injL = InjLt x
                 injR = InjRt y
                 xy = PairTerm x y
                 iso = IsoVar "exampleIso"
                 omega = Omega iso y
                 letT = Let (Xprod "x") omega x
                 comb = CombTerms x y
                 alpha1 = AlphaTerm (1:+0) x
                 alpha2 = AlphaTerm (1:+0) y
                 comb2 = CombTerms alpha1 alpha2
                 isoType = Iso bool bool
                 delta = [("y",bool)]
                 delta2 = [("y",bool),("x",bool)]
                 psi = [("exampleIso",isoType)]
                 in  (show letT) ++ " : " ++ show (wrap $ mytermTypeCheck delta psi letT bool) ++ "\n"
                        ++ (show comb) ++ ": " ++ show (wrap $ mytermTypeCheck delta2 psi comb bool) ++ "\n"
                          ++ (show comb2) ++ ": " ++ show (wrap $ mytermTypeCheck delta2 psi comb2 bool) ++ "\n"

testNotEval :: String
testNotEval = let  bool = Sum One One
                   tt = InjR EmptyV
                   ttTerm = InjRt EmptyTerm
                   ff = InjL EmptyV
                   ffTerm = InjLt EmptyTerm
                   ttE = Val tt
                   ffE = Val ff
                   alpha1 = AlphaVal (1:+0) ttE
                   alpha2 = AlphaVal (0:+0) ttE
                   alpha3 = AlphaVal (1:+0) ffE
                   e1 = Combination alpha1 alpha2
                   e2 = Combination alpha2 alpha3
                   notE = Clauses [(ff,e1),(tt,e2)]
                   check = Omega notE ttTerm
                   check2 = Omega notE ffTerm
              in show (applicativeContext check) ++ "\n"
                    ++ show (applicativeContext check2)

main = do
        putStr ("tests: if | map | had | mapAcc | cnot | terms --Input quit to stop.\n ")
        f <- getLine
        case f of
          "had" -> putStr testHad
          "if" ->  putStr test1
          "map" -> putStr testMap
          "mapAcc" -> putStr testMapAcc
          "cnot" -> putStr testCnot
          "terms" -> putStr testTerms
          "a" -> putStr testNotEval
          "quit" -> exitSuccess
          otherwise -> putStr "That function is not defined!!"
        putStr "\n\n\n"
        main
