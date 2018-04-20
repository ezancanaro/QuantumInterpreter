module IsoDefinitions where

import AbstractData
import Utils

import Data.Complex
import Data.Number.CReal





hadIso :: (Iso,T)
hadIso = let a1 = (1/sqrt(2))::CReal
             a2 = (-1/sqrt(2))::CReal --fixed precision numbers
             alpha = (a1 :+ 0)
             beta = (a2 :+ 0) -- complex numbers
             eTT = Val tt --ExtendedValue true
             eFF = Val ff --ExtendedValue false
             e1 = Combination (AlphaVal alpha eTT) (AlphaVal alpha eFF) -- Clause 1
             e2 = Combination (AlphaVal alpha eTT) (AlphaVal beta eFF)  -- Clause 2
             had = Clauses [(tt,e1),(ff,e2)] --
             isoType = Iso bool bool --Type of Had iso
             in (had,isoType)

if1 :: (Iso,T)
if1 = let   x = Xval "x"
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
            ifIso = Lambda "g" lambdaH
            a = One
            b = One
            boolXa = Prod bool a
            boolXb = Prod bool b
            isoAb = (Iso a b)
            t2 = Iso boolXa boolXb
            isoT1 = Comp a b t2
            isoType = Comp a b isoT1
            in (ifIso ,isoType)

map1 :: (Iso,T)
map1 =let   a = TypeVar 'a'
            b = TypeVar 'b'
            n = Xval "n"
            m = Xval "m"
            h = Xval "h"
            t = Xval "t"
            recursiveA = Rec a
            recursiveB = Rec b
            emptyList = InjL EmptyV
            l1 = InjR (PairV emptyList emptyList)
            l2 = InjR (PairV h t)
            e1 = (Combination (AlphaVal (1:+0)(Val emptyList)) (AlphaVal (0:+0) (Val emptyList)))
            f = IsoVar "f"
            g = IsoVar "g"
            eE = LetE (Xprod "m") f (Xprod "t")
                    (Combination (AlphaVal (0:+0) (Val emptyList)) (AlphaVal (1:+0)(Val (InjR $ PairV n m))))
            e2 = LetE (Xprod "n") g (Xprod "h") eE
            func = Clauses [(emptyList,e1),(l2,e2)]
            fixPf = Fixpoint "f" func
            mapIso = Lambda "g" fixPf
            funType = Iso recursiveA recursiveB
            isoType = Comp a b funType
            in (mapIso,isoType)

mapAccIso :: (Iso,T)
mapAccIso=
        let a = bool
            b = bool
            c = bool
            x' = Xval "x'"
            y' = Xval "y'"
            h1 = Xval "h1"
            t1 = Xval "t1"
            z = Xval "z"
            h' = Xval "h'"
            t' = Xval "t'"
            recursiveC = Rec c
            recursiveB = Rec b
            emptyList = InjL EmptyV
            xEmpty = PairV x' emptyList
            tl = PairV t1 emptyList
            ht = InjR (PairV h1 t1)
            xHT = PairV x' ht

            yh' = PairP (Xprod "y'") (Xprod "h'")
            xh = PairP (Xprod "x'") (Xprod "h1")
            yt = PairP (Xprod "y'") (Xprod "t1")
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
            mapAccIso = Lambda "g" fixPf

            aXb = Prod a b
            aXc = Prod a c
            aXrecB = Prod a recursiveB
            aXrecC = Prod a recursiveC
            gType = Iso aXb aXc
            funType = Iso aXrecB aXrecC

            isoType = Comp aXb aXc funType

            in (mapAccIso,isoType)

cnotIso :: (Iso,T)
cnotIso =
       let  recBool = Rec bool
            recBoolXbool = Prod recBool bool
            emptyList = InjL EmptyV
            tb = Xval "tb"
            cbs = Xval "cbs"
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
            cnotIso = Fixpoint "f" fun

            isoType = Iso recBoolXbool recBoolXbool

            in (cnotIso,isoType)

not1 :: (Iso,T)
not1 = let  ttTerm = InjRt EmptyTerm
            ffTerm = InjLt EmptyTerm
            alpha1 = AlphaVal (1:+0) ttE
            alpha2 = AlphaVal (0:+0) ttE
            alpha3 = AlphaVal (1:+0) ffE
            e1 = Combination alpha1 alpha2
            e2 = Combination alpha2 alpha3
            notIso = Clauses [(ff,e1),(tt,e2)]
            isoType = Iso bool bool
            in (notIso,isoType)

simpleCnot :: (Iso,T)
simpleCnot = let v1 = PairV (InjL EmptyV) (Xval "x")
                 v2 = PairV (InjR EmptyV) (Xval "x")
                 l2 = (LetE (Xprod "z") (IsoVar "f") (Xprod "x") (Val $ PairV (InjR EmptyV) (Xval "z")))
                 alpha1 = AlphaVal (1:+0) (Val v1)
                 alpha2 = AlphaVal (1:+0) l2
                 e1 = Combination alpha1 (AlphaVal (0:+0) e2)
                 e2 = Combination (AlphaVal (0:+0) (Val v1)) alpha2
                 clauses = Clauses [(v1,e1),(v2,e2)]
                 cnot = Lambda "f" clauses
                 cnotType = Iso (Prod bool bool) (Prod bool bool)
                 in (cnot,cnotType)

idIso:: (Iso,T)
idIso = let v1 = tt
            v2 = ff
            e1 = Combination (AlphaVal (1:+0) (Val tt)) (AlphaVal (0:+0) (Val ff))
            e2 = Combination (AlphaVal (0:+0) (Val tt)) (AlphaVal (1:+0) (Val ff))
            clauses = Clauses [(v1,e1),(v2,e2)]
            ty = Iso bool bool
            in (clauses,ty)

constant :: (Iso,T) --Not a valid isomorphism in the language.!!
constant = let  v1 = tt
                v2 = ff
                e1 = Combination (AlphaVal (1:+0) (Val tt)) (AlphaVal (0:+0) (Val tt))
                e2 = Combination (AlphaVal (0:+0) (Val tt)) (AlphaVal (1:+0) (Val tt))
                clauses = Clauses [(v1,e1),(v2,e2)]
                ty = Iso bool bool
                in (clauses,ty)

-- This iso will only work for a balanced 1 bit function. A constant function on 1 bit would need to be refactored into a 2-bit function to be reversible.
-- The same can be said for oracles acting on more than 1 bit.
-- If we cannot express irreversible functions in the language, a new oracle Iso needs to be built for every function f.
-- The general structure of each oracle would be similar to the iso defined here, but the action of F would be hard-coded instead of the Let-expression.
oracle2 :: (Iso,T)
oracle2 = let (cnot,_) = simpleCnot
              (mynot,_) = not1
              v1 = PairV (Xval "x") (tt)
              v2 = PairV (Xval "x") (ff)
              c1 = Val $ PairV (Xval "x") (Xval "w")
              c1' = Combination (AlphaVal (1:+0) c1) (AlphaVal (0:+0) c1)
              c1'' = Combination (AlphaVal (0:+0) c1) (AlphaVal (1:+0) c1)
              e1 = LetE (Xprod "w") (IsoVar "f") (Xprod "x") c1'
              e2 = LetE (Xprod "w") mynot (Xprod "z") c1''
              e2' = LetE (Xprod "z") (IsoVar "f") (Xprod "x") e2
              clauses = Clauses [(v1,e1),(v2,e2')]
              oracle2 = Lambda "f" clauses
              ty = Iso (Prod bool bool) (Prod bool (Prod bool bool)) -- Not the right type!!
              in (oracle2,ty)

deutsch :: (Iso,T)
deutsch = let v1 = PairV (Xval "x") (Xval "y")
              e1 = LetE (Xprod "h1") (IsoVar "had") (Xprod "x") e2
              e2 = LetE (Xprod "h2") (IsoVar "had") (Xprod "y") e3
              e3 = LetE (Xprod "q") (IsoVar "Oracle") (PairP (Xprod "h1") (Xprod "h2")) e4
              e4 = LetE (Xprod "out") (IsoVar "hadX") (Xprod "q") e5
              e5 = AlphaVal (1:+0) (Val $ Xval "out")
              clauses = Clauses [(v1,e1)]
              iso = Lambda "had" (Lambda "Oracle" (Lambda "hadX" clauses))
              ty  = Iso (Prod bool bool) (Prod bool bool)
              isoType = Comp (bool) (bool) $ Comp (Prod bool bool) (Prod bool bool)  $ Comp (Prod bool bool) (Prod bool bool) ty
              in (iso,isoType)

--For instance, an oracle implementing a constant function on 2 bits could be built as::
oracleConstant3Bits :: (Iso,T)
oracleConstant3Bits = let
                          (mynot,_) = not1
                          v1 = PairV (tt) (PairV tt tt)
                          v2 = PairV (tt) (PairV ff tt)
                          v3 = PairV (ff) (PairV tt tt)
                          v4 = PairV (ff) (PairV ff tt)
                          v5 = PairV (tt) (PairV tt ff)
                          v6 = PairV (tt) (PairV ff ff)
                          v7 = PairV (ff) (PairV tt ff)
                          v8 = PairV (ff) (PairV ff ff)

                          v1' = Val $ PairV (tt) (PairV tt tt)
                          v2' = Val $ PairV (tt) (PairV ff tt)
                          v3' = Val $ PairV (ff) (PairV tt tt)
                          v4' = Val$ PairV (ff) (PairV ff tt)
                          v5' = Val$ PairV (tt) (PairV tt ff)
                          v6' = Val$ PairV (tt) (PairV ff ff)
                          v7' = Val$ PairV (ff) (PairV tt ff)
                          v8' = Val$ PairV (ff) (PairV ff ff)
                          elist =[v1',v2',v3',v4',v5',v6',v7',v8']

                          c1 = buildOneZeroCombs elist 0 0
                          c2 = buildOneZeroCombs elist 1 0
                          c3 = buildOneZeroCombs elist 2 0
                          c4 = buildOneZeroCombs elist 3 0
                          c5 = buildOneZeroCombs elist 4 0
                          c6 = buildOneZeroCombs elist 5 0
                          c7 = buildOneZeroCombs elist 6 0
                          c8 = buildOneZeroCombs elist 7 0


                          clauses = Clauses [(v1,c1),(v2,c2),(v3,c3),(v4,c4),(v5,c5),(v6,c6),(v7,c7),(v8,c8)]
                          ty = Iso (Prod bool (Prod bool bool)) (Prod bool (Prod bool bool)) -- Not the right type!!
                          in (clauses,ty)


buildOneZeroCombs :: [E] -> Int -> Int -> E
buildOneZeroCombs (e:[]) i c
  | i == c =  AlphaVal (1:+0) e
  | otherwise =  AlphaVal (0:+0) e
buildOneZeroCombs (e:elist) i c
  | i == c =  Combination (AlphaVal (1:+0) e) (buildOneZeroCombs elist i $ c+1)
  | otherwise =  Combination (AlphaVal (0:+0) e) (buildOneZeroCombs elist i $ c+1)


hadOneOfTwo :: (Iso,T)
hadOneOfTwo = let (had,_) = hadIso
                  (myId,_) = idIso
                  v1 = PairV (Xval "x") (Xval "y")
                  e1 = LetE (Xprod "w") (had) (Xprod "x") e2
                  e2 = LetE (Xprod "z") (myId) (Xprod "y") (Val $ PairV (Xval "w") (Xval "y"))
                  clauses = Clauses [(v1,e1)]
                  ty = Iso (Prod bool bool) (Prod bool bool)
                  in (clauses,ty)

hadTwoOfThree :: (Iso,T)
hadTwoOfThree = let (had12,_) = hadTensorId
                    ett = Val tt
                    eff = Val ff

                    v1 = PairV tt (Xval "y")
                    v2 = PairV ff (Xval "y")
                    ePair1 = Val $ PairV tt (Xval "w")
                    ePair2 = Val $ PairV ff (Xval "w")
                    comb1 = Combination (AlphaVal alpha ePair1) (AlphaVal alpha ePair2)
                    comb2 = Combination (AlphaVal alpha ePair1) (AlphaVal beta ePair2)
                    e1 = LetE (Xprod "w") had12 (Xprod "y") comb1
                    e2 = LetE (Xprod "w") had12 (Xprod "y") comb2
                    clau = Clauses [(v1,e1),(v2,e2)]
                    ty = Iso (Prod bool bool) (Prod bool bool)
                    in (clau,ty)

hadThreeOfFour :: (Iso,T)
hadThreeOfFour = let  (had23,_) = hadTwoOfThree
                      ett = Val tt
                      eff = Val ff

                      v1 = PairV tt (Xval "y")
                      v2 = PairV ff (Xval "y")
                      ePair1 = Val $ PairV tt (Xval "w")
                      ePair2 = Val $ PairV ff (Xval "w")
                      comb1 = Combination (AlphaVal alpha ePair1) (AlphaVal alpha ePair2)
                      comb2 = Combination (AlphaVal alpha ePair1) (AlphaVal beta ePair2)
                      e1 = LetE (Xprod "w") had23 (Xprod "y") comb1
                      e2 = LetE (Xprod "w") had23 (Xprod "y") comb2
                      clau = Clauses [(v1,e1),(v2,e2)]
                      ty = Iso (Prod bool bool) (Prod bool bool)
                      in (clau,ty)

hadFourOfFive :: (Iso,T)
hadFourOfFive = let (had34,_) = hadThreeOfFour
                    ett = Val tt
                    eff = Val ff

                    v1 = PairV tt (Xval "y")
                    v2 = PairV ff (Xval "y")
                    ePair1 = Val $ PairV tt (Xval "w")
                    ePair2 = Val $ PairV ff (Xval "w")
                    comb1 = Combination (AlphaVal alpha ePair1) (AlphaVal alpha ePair2)
                    comb2 = Combination (AlphaVal alpha ePair1) (AlphaVal beta ePair2)
                    e1 = LetE (Xprod "w") had34 (Xprod "y") comb1
                    e2 = LetE (Xprod "w") had34 (Xprod "y") comb2
                    clau = Clauses [(v1,e1),(v2,e2)]
                    ty = Iso (Prod bool bool) (Prod bool bool)
                    in (clau,ty)


had4 :: (Iso,T)
had4 = let  (had1,_) = hadIso
            b = Xval "b"
            n = Xval "n"
            m = Xval "m"
            k = Xval "k"
            b' = Xval "b'"
            n' = Xval "n'"
            m' = Xval "m'"
            k' = Xval "k'"
            v1 = PairV b (PairV n (PairV m k))
            ef = Val $ PairV b' (PairV n' (PairV m' k'))
            e1 = LetE (Xprod "b'") had1 (Xprod "b") e2
            e2 = LetE (Xprod "n'") had1 (Xprod "n") e3
            e3 = LetE (Xprod "m'") had1 (Xprod "m") e4
            e4 = LetE (Xprod "k'") had1 (Xprod "k") ef
            fourBits = Prod bool (Prod bool (Prod bool bool))
            clauses = Clauses [(v1,e1)]
            ty = Iso fourBits fourBits
            in (clauses,ty)
had5 :: (Iso,T)
had5 = let  (had1,_) = hadIso
            b = Xval "b"
            n = Xval "n"
            m = Xval "m"
            k = Xval "k"
            y = Xval "y"
            b' = Xval "b'"
            n' = Xval "n'"
            m' = Xval "m'"
            k' = Xval "k'"
            y' = Xval "y'"
            v1 = PairV b (PairV n (PairV m (PairV k y)))
            ef = Val $ PairV b' (PairV n' (PairV m' (PairV k' y')))
            e1 = LetE (Xprod "b'") had1 (Xprod "b") e2
            e2 = LetE (Xprod "n'") had1 (Xprod "n") e3
            e3 = LetE (Xprod "m'") had1 (Xprod "m") e4
            e4 = LetE (Xprod "k'") had1 (Xprod "k") e5
            e5 = LetE (Xprod "y'") had1 (Xprod "y") ef
            fiveBits = Prod (Prod bool (Prod bool (Prod bool bool))) bool
            clauses = Clauses [(v1,e1)]
            ty = Iso fiveBits fiveBits
            in (clauses,ty)


hadTensorId :: (Iso,T)
hadTensorId = let ett = Val tt
                  eff = Val ff
                  (myId,_) = idIso
                  v1 = PairV tt (Xval "y")
                  v2 = PairV ff (Xval "y")
                  ePair1 = Val $ PairV tt (Xval "w")
                  ePair2 = Val $ PairV ff (Xval "w")
                  comb1 = Combination (AlphaVal alpha ePair1) (AlphaVal alpha ePair2)
                  comb2 = Combination (AlphaVal alpha ePair1) (AlphaVal beta ePair2)
                  e1 = LetE (Xprod "w") myId (Xprod "y") comb1
                  e2 = LetE (Xprod "w") myId (Xprod "y") comb2
                  clau = Clauses [(v1,e1),(v2,e2)]

                  ty = Iso (Prod bool bool) (Prod bool bool)
                  in (clau,ty)



grover3 :: (Iso,T)
grover3 = let a = Xval "a"
              b = Xval "b"
              c = Xval "c"
              v1 = PairV b (PairV ff (PairV c tt))
              v2 = PairV b (PairV tt (PairV c tt))
              v3 = PairV b (PairV ff (PairV c ff))
              v4 = PairV b (PairV tt (PairV c ff))

              v1' = Val $ PairV b (PairV ff (PairV c ff))
              v2' = Val $ PairV b (PairV tt (PairV c tt))
              v3' = Val $ PairV b (PairV ff (PairV c tt))
              v4' = Val $ PairV b (PairV tt (PairV c ff))
              elist = [v1',v2',v3',v4']
              c1 = buildOneZeroCombs elist 0 0
              c2 = buildOneZeroCombs elist 1 0
              c3 = buildOneZeroCombs elist 2 0
              c4 = buildOneZeroCombs elist 3 0
              clauses = Clauses [(v1,c1),(v2,c2),(v3,c3),(v4,c4)]
              fourBits = Prod bool (Prod bool (Prod bool bool))
              ty = Iso fourBits fourBits
              in (clauses,ty)

conditionalPhase4 :: (Iso,T)
conditionalPhase4 = let     a = Xval "a"
                            b = Xval "b"
                            c = Xval "c"
                            d = Xval "d"
                            v1 = PairV tt (PairV tt (PairV tt d))
                            v2 = PairV a (PairV b (PairV c d))
                            v1' = AlphaVal ((-1):+0) $ Val v1
                            v2' = AlphaVal (1:+0) $ Val v2
                            v1'0 = AlphaVal (0:+0) $ Val v1
                            v2'0 = AlphaVal (0:+0) $ Val v2
                            c1 = Combination v1' v2'0
                            c2 = Combination v1'0 v2'
                            clauses = Clauses [(v1,c1),(v2,c2)]
                            fourBits = Prod bool (Prod bool (Prod bool bool))
                            ty = Iso fourBits fourBits
                            in (clauses,ty)

-- Oracle that recognizes ints (__1_)  as solutions
simplifiedGroverOracle :: (Iso,T)
simplifiedGroverOracle = let a = Xval "a"
                             b = Xval "b"
                             c = Xval "c"
                             v1 = PairV a (PairV b (PairV ff (PairV c tt)))
                             v2 = PairV a (PairV b (PairV tt (PairV c tt)))

                             v3 = PairV a (PairV b (PairV ff (PairV c ff)))
                             v4 = PairV a (PairV b (PairV tt (PairV c ff)))

                             v1' = Val $ PairV a (PairV b (PairV ff (PairV c ff)))
                             v2' = Val $ PairV a (PairV b (PairV tt (PairV c tt)))

                             v3' = Val $ PairV a (PairV b (PairV ff (PairV c tt)))
                             v4' = Val $ PairV a (PairV b (PairV tt (PairV c ff)))

                             fiveBits = Prod bool (Prod bool (Prod bool (Prod bool bool)))
                             ty = Iso fiveBits fiveBits
                             elist = [v1',v2',v3',v4']
                             c1 = buildOneZeroCombs elist 0 0
                             c2 = buildOneZeroCombs elist 1 0
                             c3 = buildOneZeroCombs elist 2 0
                             c4 = buildOneZeroCombs elist 3 0
                             clauses = Clauses [(v1,c1),(v2,c2),(v3,c3),(v4,c4)]
                             in (clauses,ty)

conditionalPhaseShift:: (Iso,T)
conditionalPhaseShift = let a = Xval "a"
                            b = Xval "b"
                            c = Xval "c"
                            d = Xval "d"
                            y = Xval "y"
                            v1 = PairV tt (PairV tt (PairV tt (PairV tt y)))
                            v2 = PairV a (PairV b (PairV c (PairV d y)))
                            v1' = AlphaVal ((-1):+0) $ Val v1
                            v2' = AlphaVal (1:+0) $ Val v2
                            v1'0 = AlphaVal (0:+0) $ Val v1
                            v2'0 = AlphaVal (0:+0) $ Val v2
                            c1 = Combination v1' v2'0
                            c2 = Combination v1'0 v2'
                            clauses = Clauses [(v1,c1),(v2,c2)]
                            fiveBits = Prod bool (Prod bool (Prod bool (Prod bool bool)))
                            ty = Iso fiveBits fiveBits
                            in (clauses,ty)


p [] [] = []
p (v:vlist) (c:clist) = (v,c) : p vlist clist

isoNext :: (Iso,T)
isoNext = let vList = [fl $ buildInt i 4 'v' | i <- [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] ]
              eList = [Val $ fl $ buildInt i 4 'v' | i <- [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,0] ]
              cList = [buildOneZeroCombs eList i 0 | i <- [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] ]
              clauses = Clauses (p vList cList)
              bitsN = (Prod bool (Prod bool (Prod bool bool)))
              ty = Iso bitsN bitsN
              in (clauses,ty)

isoPrevious :: (Iso,T)
isoPrevious = let vList = [fl $ buildInt i 4 'v' | i <- [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] ]
                  eList = [Val $ fl $ buildInt i 4 'v' | i <- [15,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] ]
                  cList = [buildOneZeroCombs eList i 0 | i <- [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] ]
                  clauses = Clauses (p vList cList)
                  bitsN = (Prod bool (Prod bool (Prod bool bool)))
                  ty = Iso bitsN bitsN
                  in (clauses,ty)

nextSigned :: (Iso,T)
nextSigned = let zero = fl $ buildInt 0 4 'v'
                 v1 = PairV ff zero
                 v2 = PairV ff (Xval "y")
                 v3 = PairV tt (Xval "y")
                 a1 = Val $ PairV (tt) (fl $ buildInt 1 4 'v')
                 a2 = Val $ PairV (ff) (Xval "y'")
                 a3 = Val $ PairV (tt) (Xval "y'")
                 alist = [a1,a2,a3]
                 c1 = Combination (AlphaVal (1:+0) a1) (Combination (AlphaVal (0:+0) a1) (AlphaVal (0:+0) a1)) --buildOneZeroCombs alist 0 0
                 c2 = buildOneZeroCombs alist 1 0
                 c3 = buildOneZeroCombs alist 2 0
                 e1 = c1
                 e2 = LetE (Xprod "y'") (IsoVar "prev") (Xprod "y") c2
                 e3 = LetE (Xprod "y'") (IsoVar "next") (Xprod "y") c3
                 clauses = Clauses [(v1,e1),(v2,e2),(v3,e3)]
                 iso = Lambda "next" (Lambda "prev" clauses)

                 bitsN = (Prod bool (Prod bool (Prod bool bool)))

                 fiveBits = Prod bool (Prod bool (Prod bool (Prod bool bool)))
                 ty = Comp bitsN bitsN (Comp bitsN bitsN $ Iso fiveBits fiveBits)
                 in (iso,ty)

prevSigned:: (Iso,T)
prevSigned = let zero = fl $ buildInt 0 4 'v'
                 v1 = PairV tt zero
                 v2 = PairV tt (Xval "x")
                 --v3 = PairV ff zero
                 v3 = PairV ff (Xval "x")

                 a1 = Val $ PairV (ff) (fl $ buildInt 1 4 'v')
                 a2 = Val $ PairV (tt) (Xval "x'")
                 --a4 = Val $ PairV (ff) (fl $ buildInt 1 4 'v')
                 a3 = Val $ PairV (ff) (Xval "x'")


                 alist = [a1,a2,a3]
                 c1 = Combination (AlphaVal (1:+0) a1) (Combination (AlphaVal (0:+0) a1) (AlphaVal (0:+0) a1))--buildOneZeroCombs alist 0 0
                 c2 = buildOneZeroCombs alist 1 0
                 c3 = buildOneZeroCombs alist 2 0
                 e1 = c1
                 e2 = LetE (Xprod "x'") (IsoVar "prev") (Xprod "x") c2
                 e3 = LetE (Xprod "x'") (IsoVar "prev") (Xprod "x") c3
                 clauses = Clauses [(v1,e1),(v2,e2),(v3,e3)]
                 iso = Lambda "next" (Lambda "prev" clauses)

                 bitsN = (Prod bool (Prod bool (Prod bool bool)))

                 fiveBits = Prod bool (Prod bool (Prod bool (Prod bool bool)))
                 ty = Comp bitsN bitsN (Comp bitsN bitsN $ Iso fiveBits fiveBits)
                 in (iso,ty)

walkTIso :: (Iso,T)
walkTIso = let v1 = PairV tt (Xval "n")
               v2 = PairV ff (Xval "n")
               a1 = Val $ PairV tt (Xval "n'")
               a2 = Val $ PairV ff (Xval "n'")
               c1 = buildOneZeroCombs [a1,a2] 0 0
               c2 = buildOneZeroCombs [a1,a2] 1 0
               e1 = LetE (Xprod "n'") (IsoVar "prevSigned") (Xprod "n") c1
               e2 = LetE (Xprod "n'") (IsoVar "nextSigned") (Xprod "n") c2
               clauses = Clauses [(v1,e1),(v2,e2)]
               iso = Lambda "prevSigned" (Lambda "nextSigned" clauses)
               fiveBits = Prod bool (Prod bool (Prod bool (Prod bool bool)))
               walkBits = Prod bool fiveBits
               ty = Iso walkBits walkBits
               (_,prevTy) = prevSigned
               (_,nextTy) = nextSigned
               actualType = Comp fiveBits fiveBits (Comp fiveBits fiveBits ty)
               in (iso,actualType)

walkTransform :: (Iso,T)
walkTransform = let (hadTIhp,_) = hadTensorIHp
                    v1 = Xval "x"
                    e2 = LetE (Xprod "w") (IsoVar "T") (Xprod "h") (Val $ Xval "w")
                    e1 = LetE (Xprod "h") (IsoVar "hadXI_hp") (Xprod "x") e2
                    clauses = Clauses [(v1,e1)]
                    fiveBits = Prod bool (Prod bool (Prod bool (Prod bool bool)))
                    walkBits = Prod bool fiveBits
                    ty = Iso walkBits walkBits
                    iso = Lambda "T" (Lambda "hadXI_hp" clauses)
                    in (iso,ty)

id4bits :: (Iso,T)
id4bits = let v1 = PairV tt (PairV (Xval "x") (PairV (Xval "y") (Xval "z")))
              v2 = PairV ff (PairV (Xval "x") (PairV (Xval "y") (Xval "z")))
              e1 = Combination (AlphaVal (1:+0) (Val v1)) (AlphaVal (0:+0) (Val v2))
              e2 = Combination (AlphaVal (0:+0) (Val v1)) (AlphaVal (1:+0) (Val v2))
              clauses = Clauses [(v1,e1),(v2,e2)]
              bitsN = (Prod bool (Prod bool (Prod bool bool)))
              ty = Iso bitsN bitsN
              in (clauses,ty)

hadTensorIHp :: (Iso,T)
hadTensorIHp = let  ett = Val tt
                    eff = Val ff
                    (myId,_) = id4bits
                    v1 = PairV tt (Xval "y")
                    v2 = PairV ff (Xval "y")
                    ePair1 = Val $ PairV tt (Xval "w")
                    ePair2 = Val $ PairV ff (Xval "w")
                    comb1 = Combination (AlphaVal alpha ePair1) (AlphaVal alpha ePair2)
                    comb2 = Combination (AlphaVal alpha ePair1) (AlphaVal beta ePair2)
                    e1 = LetE (Xprod "w") myId (Xprod "y") comb1
                    e2 = LetE (Xprod "w") myId (Xprod "y") comb2
                    clau = Clauses [(v1,e1),(v2,e2)]

                    ty = Iso (Prod bool bool) (Prod bool bool)
                    in (clau,ty)


hadAllButOne :: (Iso,T)
hadAllButOne =let ett = Val tt
                  eff = Val ff
                  --(myId,_) = idIso
                  v1 = InjR (PairV (Xval "x") (InjL EmptyV))
                  v2 = InjR (PairV tt (Xval "y"))
                  v3 = InjR (PairV ff (Xval "y"))

                  ePair1 = Val $ InjR $ PairV (Xval "z") (InjL EmptyV)
                  ePair2 = Val $ InjR $ PairV tt (Xval "w")
                  ePair3 = Val $ InjR $ PairV ff (Xval "w")

                  comb1 = buildOneZeroCombs [ePair1,ePair1,ePair1] 0 0
                  comb2 = Combination (AlphaVal (0:+0) ePair2) $ Combination (AlphaVal alpha ePair2) (AlphaVal alpha ePair3)
                  comb3 = Combination (AlphaVal (0:+0) ePair2) $ Combination (AlphaVal alpha ePair2) (AlphaVal beta ePair3)
                  e1 = LetE (Xprod "z") (IsoVar "id") (Xprod "x") comb1
                  e2 = LetE (Xprod "w") (IsoVar "f") (Xprod "y") comb2
                  e3 = LetE (Xprod "w") (IsoVar "f") (Xprod "y") comb3
                  clau = Clauses [(v1,e1),(v2,e2),(v3,e3)]
                  iso = Lambda "id" $ Fixpoint "f" clau
                  ty = Comp bool bool $ Iso (Rec bool) (Rec bool)
                  in (iso,ty)

-- groverExOracle :: (Iso,T)
-- groverExOracle = let (mynot,_) = not1
--                      v1 = PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v2 = PairV (PairV tt (PairV tt (PairV tt ff))) tt
--                      v3 = PairV (PairV tt (PairV tt (PairV ff tt))) tt
--                      v4 = PairV (PairV tt (PairV tt (PairV ff ff))) tt
--
--                      v5 = PairV (PairV tt (PairV ff (PairV tt tt))) tt
--                      v6 = PairV (PairV tt (PairV ff (PairV tt ff))) tt
--                      v7 = PairV (PairV tt (PairV ff (PairV ff tt))) tt
--                      v8 = PairV (PairV tt (PairV ff (PairV ff ff))) tt
--
--                      v9 = PairV (PairV ff (PairV tt (PairV tt tt))) tt
--                      v10 = PairV (PairV ff (PairV tt (PairV tt ff))) tt
--                      v11 = PairV (PairV ff (PairV tt (PairV ff tt))) tt
--                      v12 = PairV (PairV ff (PairV tt (PairV ff ff))) tt
--                      v13 = PairV (PairV ff (PairV ff (PairV tt tt))) tt
--                      v14 = PairV (PairV ff (PairV ff (PairV tt ff))) tt
--                      v15 = PairV (PairV ff (PairV ff (PairV ff tt))) tt
--                      v16 = PairV (PairV ff (PairV ff (PairV ff ff))) tt
--
--                      v17 = PairV (PairV tt (PairV tt (PairV tt tt))) ff
--                      v18 = PairV (PairV tt (PairV tt (PairV tt ff))) ff
--                      v19 = PairV (PairV tt (PairV tt (PairV ff tt))) ff
--                      v20 = PairV (PairV tt (PairV tt (PairV ff ff))) ff
--
--                      v21 = PairV (PairV tt (PairV ff (PairV tt tt))) ff
--                      v22 = PairV (PairV tt (PairV ff (PairV tt ff))) ff
--                      v23 = PairV (PairV tt (PairV ff (PairV ff tt))) ff
--                      v24 = PairV (PairV tt (PairV ff (PairV ff ff))) ff
--
--                      v25 = PairV (PairV ff (PairV tt (PairV tt tt))) ff
--                      v26 = PairV (PairV ff (PairV tt (PairV tt ff))) ff
--                      v27 = PairV (PairV ff (PairV tt (PairV ff tt))) ff
--                      v28 = PairV (PairV ff (PairV tt (PairV ff ff))) ff
--                      v29 = PairV (PairV ff (PairV ff (PairV tt tt))) ff
--                      v30 = PairV (PairV ff (PairV ff (PairV tt ff))) ff
--                      v31 = PairV (PairV ff (PairV ff (PairV ff tt))) ff
--                      v32 = PairV (PairV ff (PairV ff (PairV ff ff))) ff
--
--
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--                      v1' = Val $ PairV (PairV tt (PairV tt (PairV tt tt))) tt
--
--                       --8' = Val$ PairV (ff) (PairV ff ff)
--                       elist =[v1',v2',v3',v4',v5',v6',v7',v8']
--
--                       c1 = buildOneZeroCombs elist 0 0


-- How to build fuinctions working on ints???
-- Take it as binary representation maybe?? Solves the problem of it being a recursive type. Choose a number of bytes and go with it.
 -- plus :: (Iso,T) -- This iso will not work because recursion is only defined for lists. Changing the int representation to a list will make it possible.
 -- plus = let zero = (intRep . dec2bin) 0
 --            suc =
 --            n = Xval "n"
 --            m = Xval "m"
 --            h = Xval "h"
 --            t = Xval "t"
 --            x = Xval "x"
 --            y = Xval "y"
--             v1 = PairV zero y
--             v2 = PairV (InjR (PairV x t)) y
--             l1 = InjR (PairV emptyList emptyList)
--             l2 = InjR (PairV h t)  suc = InjR $ PairV (InjR EmptyV) (Xval "s")
-- --            p = IsoVar "p"
--            l = Xval "l"
--            l' = Xval "l2"
--            s' = Xval "s2"
--            v1 = PairV zero l
--            e1 = Val $ PairV l l
--            v2 = PairV suc l
--            l's' = PairP  (Xprod "s2") (Xprod "l2")
--            pair2 = PairP (Xprod "s") (Xprod "l")
--            resultVal = Val $ PairV (InjR s') l'
--            lComb = Combination (AlphaVal (1:+0) e1) (AlphaVal (0+0) resultVal)
--            lComb2 = Combination (AlphaVal (0:+0) e1) (AlphaVal (1:+0) resultVal)
--            e2 = LetE l's' p pair2 lComb2
--            cl = Clauses [(v1,lComb),(v2,e2)]
--            sumIso = Fixpoint "p" cl
--            isoType = Iso One One -- What would be the type of an int representation as specified here??
--            in (sumIso,isoType)
