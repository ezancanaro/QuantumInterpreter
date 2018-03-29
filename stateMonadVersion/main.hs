{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Main where
import MonadicInt
import AbstractData
import Utils
import Semantics
import IsoDefinitions

import Data.Complex
import Numeric.Fixed
import Control.Monad
import System.Exit


instance {-# OVERLAPPING #-} Show (TypingState) where
  show (d,p) = "\n\n\tTerm Variables: " ++ show d
                  ++ "\n\n\tIso Variables: " ++ show p

--Testing case for parametrized conditional.
test1 :: String
test1 = let (ifIso,ifType) = if1
            delta = [("x",One)]
            psi = []
            (had,_) = hadIso
            term = (PairTerm (InjLt EmptyTerm) (InjLt EmptyTerm))
            check = Omega (App ifIso (App had had)) term
            evaluation = ValueT $ applicativeContext check
            if' = invertIso ifIso
            if'Type = invertType ifType
            check2 = Omega (App if' (App had had)) evaluation
            in ("If Type:" ++ show (typeCheck delta psi ifIso ifType) )
              ++ "\nTestig if, with g,h being Had\n" ++ show ifIso ++ "\n" ++  show term ++".\nEvals to:\n\t" ++ show evaluation
                ++ "\n\nInverted if: " ++ show (invertIso ifIso) ++ "Typed: " ++ show if'Type
                  ++ "\n  Evals to: " ++ show (applicativeContext check2)
              --    ++ ("\nPairType:" ++ show (mytermTypeCheck delta psi pterm (Sum bool One)))

testMap :: String
testMap =
  let (map',isoType) = map1
      delta = [("h",a),("t",recursiveA)]
      psi = []
      (had,_) = hadIso
      littleList = InjRt $ PairTerm (falseTerm)  (InjLt EmptyTerm)
      notSoLittleList = InjRt $ PairTerm (falseTerm) littleList
      list3 = boolLists [True,True,False,False]
      check = Omega (App map' had) (littleList)
      check2 = Omega (App map' had) (notSoLittleList)
      check3 = Omega (App map' had) list3
      inverseMap = invertIso map'
      inverseMapType = invertType isoType
      result = ValueT $ applicativeContext check3
      check' = Omega (App inverseMap had) result
      result' = applicativeContext check'
      in ( "\n Has Type: " ++ show (typeCheck delta psi map' isoType))
        ++  "\n\nEvaluating: " ++ show check3 ++ "\n\n\tEvals to:\n\t\t " ++ show result
          ++ "\n\n Inverse Map: " ++ show inverseMap
            ++ "\n\n Evals to: " ++ show result'

testHad :: String
testHad = let (had,isoType) = hadIso
              delta = []
              psi = []
              arg = InjLt EmptyTerm
              check = Omega had arg
              result = ValueT $ applicativeContext check
              invHad = invertIso had
              invHadType = invertType isoType
              result' = applicativeContext (Omega had result)
              in ("Iso Had::" ++ show (typeCheck delta psi had isoType) ++ "\n" ++ show had)
                ++  "Applied to" ++ show arg ++ "\n\nEvals to:\n\t " ++ show result
                  ++ "\n\nInverse Had:\n\t " ++ show invHad
                    ++ "\n\n Evals to:\n\t " ++ show result'


testMapAcc :: String
testMapAcc =  let (mapAcc,isoType) = mapAccIso
                  delta = [("x'",bool),("h1",bool),("t1",Rec bool)]
                  psi = []
                  in ("MapAcc Type: " ++ show (typeCheck delta psi mapAcc isoType))

testCnot :: String
testCnot = let  (cnot,isoType) = cnotIso
                delta = [("tb",bool),("cbs",recBool)]
                psi = [("not",Iso bool bool)]
                invCnot = invertIso cnot

                in ("Cnot: " ++ show (typeCheck delta psi cnot isoType) ++ "\n" ++ show cnot)
                  ++ "\n\nInverse:\n\t " ++ show invCnot


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

testHadHad :: String
testHadHad =  let (had,isoType) = hadIso
                  delta = []
                  psi = []
                  combVal = ValueT $ Evalue $ Combination (AlphaVal alpha (Val tt)) (AlphaVal beta (Val ff))
                  check = Omega had (combVal)
                  in ("Had Type:" ++ show (typeCheck delta psi had isoType) )
                    ++  "\n\nEvals to:\n\t " ++ show (applicativeContext check)


combinationTest :: String
combinationTest = let a1 = alpha * alpha
                      a2 = beta * alpha
                      p1 = (a1,ttE)
                      p2 = (a1,ffE)
                      p3 = (a1,ttE)
                      p4 = (a2,ffE)
                      list = [p1,p2,p3,p4]
                   in show (addAllCombinations list)

main = do
        putStr ("tests: if | map | had | hadHad| mapAcc | cnot | terms --Input quit to stop.\n ")
        f <- getLine
        case f of
          "had" -> putStr testHad
          "if" ->  putStr test1
          "map" -> putStr testMap
          "mapAcc" -> putStr testMapAcc
          "cnot" -> putStr testCnot
          "terms" -> putStr testTerms
          "a" -> putStr testNotEval
          "hadHad" -> putStr testHadHad
          "quit" -> exitSuccess
          otherwise -> putStr "That function is not defined!!"
        putStr "\n\n\n"
        --putStr $ "\n\n\n\n  CombinationTest:  " ++ combinationTest
        main
