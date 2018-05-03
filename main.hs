module Main where
import Typechecker
import AbstractData
import Utils
import Semantics
import IsoDefinitions

import Data.Complex
import Data.Number.CReal
import Control.Monad
import System.Exit


--Testing case for parametrized conditional.
test1 :: String
test1 = let (ifIso,ifType) = if1
            delta = [("x",One)]
            psi = []
            (had,_) = hadIso
            term = (PairTerm (InjLt EmptyTerm) (InjLt EmptyTerm))
            check = Omega (App ifIso (App had had)) term
            evaluation = ValueT $ startEval check
            if' = invertIso ifIso
            if'Type = invertType ifType
            check2 = Omega (App if' (App had had)) evaluation
            result2 = startEval check2
            --r3 = algebraicProperties $ tensorProductRep result2
            in ("If Type:" ++ show (typeCheck delta psi ifIso ifType) )
              ++ "\nTestig if, with g,h being Had\n" ++ show ifIso ++ "\n" ++  show term ++".\nEvals to:\n\t" ++ show evaluation
                ++ "\n\nInverted if: " ++ show (invertIso ifIso) ++ "Typed: " ++ show if'Type
                  ++ "\n  Evals to: " ++ show result2 -- ++ "\n\nTensor: " ++ show r3
              --    ++ ("\nPairType:" ++ show (mytermTypeCheck delta psi pterm (Sum bool One)))

testMap :: String
testMap =
  let (map',isoType) = map1
      delta = [("h",a),("t",recursiveA)]
      psi = []
      (had,_) = hadIso
      littleList = InjRt $ PairTerm (falseTerm)  (InjLt EmptyTerm)
      notSoLittleList = InjRt $ PairTerm (falseTerm) littleList
      list3 = boolLists [True,True,False]
      check = Omega (App map' had) (littleList)
      check2 = Omega (App map' had) (notSoLittleList)
      check3 = Omega (App map' had) list3
      inverseMap = invertIso map'
      inverseMapType = invertType isoType
      result = ValueT $ startEval check3
      check' = Omega (App inverseMap had) result
      result' = startEval check'
      ccc = applicativeContext check'
  --    curious = tensorProductRep result'
      in ( "\n Has Type: " ++ show (typeCheck delta psi map' isoType))
        ++  "\n\nEvaluating: " ++ show check3 ++ "\n\n\tEvals to:\n\t\t " ++ show result
          ++ "\n\n Inverse Map: " ++ show inverseMap
            ++ "\n\n Evals to: " ++ show result'
              -- ++ "\n\n Curiously:: " ++ show curious

--E0.354~VR_[EVE0.707~VInjL_()+VE0.707~VInjR_()
      --      : EVR_[EVE0.707~VInjL_()+VE0.707~VInjR_()
                -- : EVR_[EVE0.707~VInjL_()+VE0.707~VInjR_()
                    -- : EVInjL_()]]]

-- E0.5~VR_[InjL_()
            -- : E0.5~VR_[InjL_()
                -- : R_[InjL_()
                  -- : InjL_()]]

testHad :: String
testHad = let (had,isoType) = hadIso
              delta = []
              psi = []
              arg = InjLt EmptyTerm
              check = Omega had arg
              result = ValueT $ startEval check
              invHad = invertIso had
              invHadType = invertType isoType
              result' = startEval (Omega had result)
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
                 letT2 = Let (Xprod "x") omega letT
                 comb = CombTerms x y
                 alpha1 = AlphaTerm (1:+0) x
                 alpha2 = AlphaTerm (1:+0) y
                 comb2 = CombTerms alpha1 alpha2
                 isoType = Iso bool bool
                 delta = [("y",bool)]
                 delta2 = [("y",bool),("x",bool)]
                 psi = [("exampleIso",isoType)]
                 in  (show letT2) ++ " : " ++ show (wrap $ mytermTypeCheck delta psi letT2 bool) ++ "--- Should this even typecheck?\n"
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
              in show (startEval check) ++ "\n"
                    ++ show (startEval check2)

testHadHad :: String
testHadHad =  let (had,isoType) = hadIso
                  delta = []
                  psi = []
                  combVal = ValueT $ Evalue $ Combination (AlphaVal alpha (Val tt)) (AlphaVal beta (Val ff))
                  check = Omega had (combVal)
                  in ("Had Type:" ++ show (typeCheck delta psi had isoType) )
                    ++  "\n\nEvals to:\n\t " ++ show (startEval check)


combinationTest :: String
combinationTest = let a1 = alpha * alpha
                      a2 = beta * alpha
                      p1 = (a1,ttE)
                      p2 = (a1,ffE)
                      p3 = (a1,ttE)
                      p4 = (a2,ffE)
                      list = [p1,p2,p3,p4]
                   in show (addAllCombinations list)


tester:: String
tester = let eTT = Val tt --ExtendedValue true
             eFF = Val ff --ExtendedValue false
             a = (2:+0)
             b = ((-2):+0)
             e1 = Combination (AlphaVal a eTT) (AlphaVal a eFF) -- Clause 1
             e2 = Combination (AlphaVal a eTT) (AlphaVal a eFF)  -- Clause 2
             e3 = Combination (AlphaVal a eTT) (AlphaVal b eFF)
             pair = PairV (Evalue e1) (Evalue e2)
             pair2 = PairV (Evalue e3) pair
             tensor = tensorProductRep pair
             tensor2 = tensorProductRep pair2
             (cnot,_) = simpleCnot
             (mynot,_) = not1
             (myIf,ifType) = if1
             delta = []
             psi = []
             check = Omega (App cnot mynot) (ValueT pair)
             types = grabPatternTypesFromAnnotation (myIf,ifType)
             in --"Cnot:: " ++ show cnot ++ "  " ++ show pair ++  "\n\n " ++ show (startEval check) ++ "\n\n" ++ show types
                "Tensor product of: " ++ show pair2 ++ "\n\t " ++ show tensor2
testOracle :: String
testOracle = let eTT = Val tt --ExtendedValue true
                 eFF = Val ff --ExtendedValue false
                 e1 = Combination (AlphaVal alpha eTT) (AlphaVal alpha eFF)
                 e2 = Combination (AlphaVal alpha eTT) (AlphaVal beta eFF)
                 pair = PairV (Evalue e1) (tt)
                 p1 = Combination (AlphaVal beta eTT) (AlphaVal alpha eFF)
                 pairTest = PairV (Evalue p1) (Evalue e2)
                 (oracle,_) = oracle2
                 (mynot,_) = not1
                 check = Omega (App oracle mynot) (ValueT pair)
                 result = startEval check
                 check2 = Omega (App oracle mynot) (ValueT result)
                 result2 = startEval check2
                -- test = tensorProductRepresentation $ Val result
                 deutschJozsa = PairV (Evalue e1) (Evalue e2)
                 checkDeutschJozsa = Omega (App oracle mynot) (ValueT deutschJozsa)
                 result3 = startEval checkDeutschJozsa
                 (had1in2,_) = hadOneOfTwo
                 (hadTensID,hadTIdType) = hadTensorId
                 check4 = Omega hadTensID (ValueT result3)
                 check5 = Omega hadTensID (ValueT pairTest)
                 result4 = startEval check4
                 result5 = startEval check5
                 tensor4 = tensorProductRep result4
                 (myId,_) = idIso
                 (cst,_) = constant

                 checkWithID = Omega (App oracle cst) (ValueT deutschJozsa)
                 resultID = startEval checkWithID
                 withIDstep2 = Omega had1in2 (ValueT resultID)
                 resultID2 = startEval withIDstep2

                 checkNew = Omega hadTensID (ValueT pairTest)
                 resultNew = startEval checkNew

                 orac = (App oracle mynot)
                 (had,_) = hadIso
                 (dst,tyDst) = deutsch
                 delta = grabPatternTypesFromAnnotation (dst,tyDst)
                 typeC = typeCheck delta [] dst tyDst
                 input = ValueT $ PairV tt ff
                 checkDst = Omega (App dst (App had (App orac hadTensID))) input
                 resultDst = startEval checkDst
                 inverse = invertIso (App dst (App had (App orac hadTensID))) -- Inversion is not working properly yet. Need to check it.
                 checkInv = Omega inverse $ ValueT resultDst
                 resultInv = startEval checkInv

                 -- te = equivalentStates (Val resultNew)
                 -- te' = tensorProductRepresentation te

                 in "Deutsch's algorithm with balanced oracle: \n" ++ show dst ++ "\nTypechecks to: " ++ show typeC
                      ++ "\n\nApplied to initial state: " ++ show input ++ "\n\n" ++ show resultDst
                      --  ++"\n---------------\n\n Inverted iso: \n" ++ show inverse ++ "Applied to previous result:\n\n" ++ show resultInv

                  -- "2qubtis Oracle, with f(x) being NOT x::\n " ++ show oracle ++ "\t" ++ show pair ++ "\n\n Evalued to:\n\t"
                  --     ++ show (result)
                  --       -- ++ "\n\nTeste:: " ++ show test
                  --        ++ "\n\n   Applied again to:" ++ show result ++ " \n\n\t" ++ show result2
                  --         ++ "DeutschJosza first-step:: " ++ show deutschJozsa ++ "\n\n\t" ++ show result3
                  --           ++ "\n\nApplying Had to x:\n" ++ show result4
                  --             -- ++ "\n\n TensorRep : " ++ show tensor4
                  --             ++ "\n-------------------------------\nApplying Had to the first qubit in " ++ show pairTest
                  --               ++ " :\n" ++ show result5
                  --                 -- ++ "\n-----------------------------------------\n"
                  --                 --   ++ "Applying step1-DeutschJosza with ID results in:: \n" ++ show resultID
                  --                 --     ++ " \n\nThen step2: \n" ++ show resultID2
                  --                           ++ "_____\n\nUsing hadTensorId:\n" ++ show hadTensID ++ "\n at pair: " ++ show pairTest
                  --                             ++ "\n\t\tresults in:\n" ++ show resultNew
                                              --  ++ "\n\n Equivalent to: " ++ show te ++ "\nwith tensor:\n" ++ show te'
--Sum -1^f(x) |x>|-> ----->  (beta tt + alpha ff)|->
-- f(tt)=ff
--f(ff)=tt



testGrover :: String
testGrover = let (gOracle,ty) = simplifiedGroverOracle
                 (mHad,_) = had5
                 delta = grabPatternTypesFromAnnotation (gOracle,ty)
                 myT = typeCheck delta [] gOracle ty
                 fourBits0 = fl $ buildInt 0 4 'v'

                 initialState = ValueT $ normalizeTuple $ PairV fourBits0 ff
                -- nT = normalizeTuple $ PairV fourBits0 ff
                 hadInitial = Omega mHad initialState
                 preparedState = startEval hadInitial
                 groverP = Omega gOracle $ ValueT preparedState
                 oracleResult = startEval groverP
                 (had45,_) = hadFourOfFive
                 hadTransf = Omega had45 $ ValueT oracleResult

                 resultHadTransf = startEval hadTransf
                 (condPhase,_) = conditionalPhaseShift
                 cond = Omega condPhase $ ValueT resultHadTransf
                 resultCondPhaseShift = startEval cond

                 (gr3,_) = grover3
                 (mHad4,_) = had4
                 bit3 = fl $ buildInt 0 3 'v'
                 initialSt3 = ValueT $ normalizeTuple $ PairV bit3 ff
                 hadIn4 = Omega mHad4 initialSt3
                 preparedState4 = startEval hadIn4
                 groverP3 = Omega gr3 $ ValueT preparedState4
                 oracleResult3 = startEval groverP3
                 (had34,_) = hadThreeOfFour
                 hadTransf3 = Omega had34 $ ValueT oracleResult3
                 resultHadTransf3 = startEval hadTransf3
                 (condPhase4,_) = conditionalPhase4
                 cond3 = Omega condPhase4 $ ValueT resultHadTransf3
                 resultCondPhaseShift3 = startEval cond3
                 -- algebra = algebraicProperties $ Val resultCondPhaseShift3
                 lastStep = Omega had34 $ ValueT resultCondPhaseShift
                 lastR = startEval lastStep

                 in "This iso needs to be properly verified. Not sure if it was built correctly."
                     ++ "simplifiedGrover\n " ++ show gr3-- ++ "\n\n Typechecks to:  " ++ show myT
                      ++ "\n\nApplied to: " ++ show preparedState4 ++ "\n\n\t Results in:\n" ++ show oracleResult3
                        ++ "\n\nHad n:: \n" ++ show resultHadTransf3 ++ "\n\n ConditionallyShifted: " ++ show resultCondPhaseShift3
                          ++ "\nFinal HadN application: \n\n" ++ show lastR


myt :: String
myt = let v1 = AlphaVal alpha $ Val $ PairV tt (Evalue $ AlphaVal (1:+0) ttE)
          v2 = AlphaVal (1:+0) ttE
          p = AlphaVal alpha $ Val $ PairV tt (Evalue $ AlphaVal (1:+0) ttE)
          pp = AlphaVal alpha $ Val $ PairV ff (Evalue $ AlphaVal (1:+0) ttE)

          comb = Combination p pp
          p1 = AlphaVal alpha $ Val $ PairV tt (Evalue comb)
          p2 = AlphaVal alpha $ Val $ PairV ff (Evalue comb)

          c = Combination p1 p2
          f= AlphaVal (0.354:+0) $ Val $ PairV tt (Evalue c)
          g = AlphaVal ((-0.354):+0) $ Val $ PairV ff (Evalue c)

          c2 = Combination f g
          tensorC = tensorProductRep (Evalue c2)
          in "V: " ++ show c2 ++ " \n\n Tensor:\n" ++ show tensorC

nextInt4 :: String
nextInt4 = let (nextInt,ty) = isoNext
               (prevInt,tyPrev) = isoPrevious
               v = fr $ buildInt 2 4 't'
               check = Omega nextInt v
               typeC = typeCheck [] [] nextInt ty
               result = startEval check
               (signedN,ty2) = nextSigned
               delta = grabPatternTypesFromAnnotation (signedN,ty2)
               typess = typeCheck delta [] signedN ty2
               v2 = PairTerm (ValueT ff) v
               check2 = Omega (App (App signedN nextInt) prevInt) v2
               result2 = startEval check2
               (prSign,tyPSign) = prevSigned
               deltaPr = grabPatternTypesFromAnnotation (prSign,tyPSign)
               typessPr = typeCheck deltaPr [] prSign tyPSign
               checkPr = Omega (App (App prSign nextInt) prevInt) v2
               resultPr = startEval checkPr
               in "Next 4bit Int: \n" ++ show nextInt ++ "\n\nTypechecks: "  ++  show typeC
                    ++ "\n\n Applied to: " ++ show v ++ "::\n" ++ show result
                      ++ "\nI'm not sure if the signed versions are well-defined: SignedNext::\n" ++ show signedN ++ "\nType: " ++ show typess
                        ++ "\n\n Applied to: " ++ show v2 ++ "::\n" ++ show result2
                          ++ "\n\n SignedPrevious:\n" ++ show prSign ++ "\nType: " ++ show typessPr
                            ++ "\n\n Applied to: " ++ show v2 ++ "::\n" ++ show resultPr

quantumWalk :: String
quantumWalk = let (walk,walkType) = walkTIso
                  (nextInt,_) = isoNext
                  (prevInt,_) = isoPrevious
                  (nextSign,_) = nextSigned
                  (prevSign,_) = prevSigned
                  typeC = typeCheck (grabPatternTypesFromAnnotation (walk,walkType)) [] walk walkType

                  prev = (App (App prevSign nextInt) prevInt)
                  p = isoReducing prev -- Should not really be needed if we can build the iso this way.
                  next = (App (App nextSign nextInt) prevInt)
                  n = isoReducing next
                  builtIso = App (App walk p) n
                    --App walk (App prevSign (App nextSign (App nextInt (App prevInt (App nextInt prevInt)))))
                  v = fr $ buildInt 0 4 't'
                  v2 = PairTerm (ValueT tt) v
                  valTest = PairTerm (ValueT tt) v2
                  check = Omega builtIso valTest
                  result = startEval check

                  (had,_) = hadIso
                  (hadIdHP,_) = hadTensorIHp
                  v3 = startEval (Omega hadIdHP valTest)
                  --v3 = PairTerm (ValueT x) v2
                  check3 = Omega builtIso $ ValueT v3
                  result3 = startEval check3
                  check4 = Omega hadIdHP $ ValueT result3
                  result4 = startEval check4
                  check5 = Omega builtIso $ ValueT result4
                  result5 = startEval check5
                  (walki,_) = walkTransform
                  --
                  in "Quantum Walk transformer T: \n" ++ show walk ++ "\nTypechecks to: " ++ show typeC
                         ++ "\n\nApplied to: " ++ show valTest ++ " :: \n\n" ++ show result
                        --  ++ "\n\nApplied to: " ++ show v3 ++ " :: \n\n" ++ show result3
                          --  ++ "\n\nHad x Ihp :\n" ++ show result4 ++ "\n Applied to T again: \n" ++ show result5
                            --  ++ "\n\n" ++ show walki


testRecHad ::String
testRecHad = let
               (recHad,tyrHad) = hadAllButOne
               (myId,_) = idIso
               delta = grabPatternTypesFromAnnotation (recHad,tyrHad)
               typeC = typeCheck delta [] recHad tyrHad
               input = boolLists [False,True,True]
               check = Omega (App recHad myId) input
               result = startEval check
               inverseId = invertIso myId
               inverseRHad = invertIso recHad
               checkInv = Omega (App inverseRHad inverseId) $ ValueT result
               resultInv = startEval checkInv
               in "Had^N of N+1 bits:: \n" ++ show recHad ++ "Typechecks to: " ++ show typeC
                    ++ "\n Applied with input: " ++ show input ++ "\n\n" ++ show result
                      ++ "\n-------------\nInverted iso: \n" ++ show inverseRHad ++ "\n\n Applied to previous result:\n\n" ++ show resultInv


--0.354~<InjL_(),
      --  0.707~<InjL_(),
          --  0.707~<InjL_(),1~InjL_()>
      --      +0.707~<InjR_(),1~InjL_()>
      -- >
      -- +0.707~<InjR_(),
          -- 0.707~<InjL_(),-- 1~InjL_()>
          -- +0.707~<InjR_(), --1~InjL_()>
            -- >
      -- >

testTest :: String
testTest = let (had23,_) = hadTwoOfThree
               (had12,_) = hadOneOfTwo
               p = Combination (AlphaVal alpha ttE) (AlphaVal alpha ffE)
               p2 = Combination (AlphaVal alpha ttE) (AlphaVal beta ffE)
               v1 = PairV (Evalue p) (PairV (Evalue p) (Evalue p2))
               r = startEval $ (Omega had23 $ ValueT v1)
               v2 = PairV (Evalue p) (Evalue p2)
               r2 = startEval $ (Omega had12 $ ValueT v2)
               in "St: " ++ show v1 ++ "\n\n goes TO:: " ++ show r
                    ++ "\n\n ST2: " ++ show v2 ++ "\n\n goest TO: " ++ show r2

typecheckProgram :: Psi -> [(Iso,T)] -> [String] -> Bool
typecheckProgram _ [] [] = True
typecheckProgram psi ((iso,ty):isoDefs) (isoName:names) = let delta = grabPatternTypesFromAnnotation (iso,ty) in
                                              if typeCheck delta psi iso ty == ty
                                                then typecheckProgram ((isoName,ty):psi) isoDefs names
                                                else False



--
-- startEval :: [(Iso,T)] -> Term -> V
-- startEval isos startPoint = error "JJJ"

ffff::String
ffff = let elist = Combination (AlphaVal (1:+0) ttE) (Combination (AlphaVal (0:+0) ttE) (Combination (AlphaVal (0:+0) ttE) $ AlphaVal (0:+0) ttE))
           in show $ pairAlphasWithValues True elist

gg :: String
gg = let  (map',isoType) = map1
          delta = [("h",a),("t",recursiveA)]
          psi = []
          (had,_) = hadIso
          list3 = boolLists [True,True]
          check3 = Omega (App map' had) list3
          result = startEval check3

          t = tensorProductRep result

          list4 = boolLists [True,True,False]
          check4 = Omega (App map' had) list4
          result4 = startEval check4

          t4 = tensorProductRep result4
          in "T1: " ++ show result ++ " = \n\n " ++ show t
                ++ "\n--------------\nT2: " ++ show result4 ++ " = \n\n " ++ show t4


testf :: E -> E -> E
testf e1 e2
  | Val v1 <- e1,
    Val v2 <- e2
      = Val v1
  | otherwise = e1


-- Loops to allow one to choose a pre-defined example.
main = do

        putStr ("tests: if | map | had | hadHad| mapAcc | cnot | terms | deutsch | grover | next | walk | recHad || quit\n ")
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
          "deutsch" -> putStr testOracle
          "grover" -> putStr testGrover
          "quit" -> exitSuccess
          "next" -> putStr nextInt4
          "walk" -> putStr quantumWalk
          "ffff" -> putStr ffff
          "gg" -> putStr gg
          "recHad" -> putStr testRecHad
          otherwise -> putStr "Undefined Function...\n\n"
        -- putStr "\n\n\n"
      --  putStr myt
        --putStr $ show (fst hadTwoOfThree)
        putStr "\n\n\n\n"

        --putStr testOracle
        --putStr $ "\n\n\n\n  CombinationTest:  " ++ combinationTest
      --  putStr $ show $ fst oracleConstant3Bits
        main
-- 0.5~<0.7071067811865475244008443621048490392848~InjL_()+0.7071067811865475244008443621048490392848~InjR_(),InjR_()>
-- +-0.5~<0.7071067811865475244008443621048490392848~InjL_()+0.7071067811865475244008443621048490392848~InjR_(),InjL_()>
-- +0.5~<0.7071067811865475244008443621048490392848~InjL_()+-0.7071067811865475244008443621048490392848~InjR_(),InjL_()>
-- +-0.5~<0.7071067811865475244008443621048490392848~InjL_()+-0.7071067811865475244008443621048490392848~InjR_(),InjR_()>
--
-- -0.5~<0.7071067811865475244008443621048490392848~InjL_()+0.7071067811865475244008443621048490392848~InjR_(),InjL_()>
-- +0.5~<0.7071067811865475244008443621048490392848~InjL_()+0.7071067811865475244008443621048490392848~InjR_(),InjR_()>
-- +0.5~<0.7071067811865475244008443621048490392848~InjL_()+-0.7071067811865475244008443621048490392848~InjR_(),InjL_()>
-- +-0.5~<0.7071067811865475244008443621048490392848~InjL_()+-0.7071067811865475244008443621048490392848~InjR_(),InjR_()>

-- Result of testingOracle::
--1/2 <|+|, injR()>  - 1/2 <|+|, InjL()> + 1/2<|-|, injL()> - 1/2<|-|,injR()>
 -- 0.5~<0.7071067811865475244008443621048490392848~InjL_()+0.7071067811865475244008443621048490392848~InjR_(),InjR_()>
--  +-0.5~<0.7071067811865475244008443621048490392848~InjL_()+0.7071067811865475244008443621048490392848~InjR_(),InjL_()>
-- +0.5~<0.7071067811865475244008443621048490392848~InjL_()+-0.7071067811865475244008443621048490392848~InjR_(),InjL_()>
-- +-0.5~<0.7071067811865475244008443621048490392848~InjL_()+-0.7071067811865475244008443621048490392848~InjR_(),InjR_()>
