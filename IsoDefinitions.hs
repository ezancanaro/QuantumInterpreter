module IsoDefinitions where

import AbstractData
import Data.Complex
import Numeric.Fixed


-- Commonly used definitions
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


hadIso :: (Iso,T)
hadIso = let a1 = toFixed (1/sqrt(2))
             a2 = toFixed (-1/sqrt(2)) --fixed precision numbers
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
                        (Combination (AlphaVal (0:+0) (Val p1)) (AlphaVal ((-1):+0) (Val p2)))
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
            e1 = (Combination (Val emptyList) (AlphaVal (0:+0) (Val emptyList)))
            f = IsoVar "f"
            g = IsoVar "g"
            eE = LetE (Xprod "m") f (Xprod "t")
                    (Combination (AlphaVal (0:+0) (Val (InjR $ PairV n m))) (Val (InjR $ PairV n m)))
            e2 = LetE (Xprod "n") g (Xprod "h") eE
            func = Clauses [(emptyList,e1),(l2,e2)]
            fixPf = Fixpoint "f" func
            mapIso = Lambda "g" fixPf
            funType = Iso recursiveA recursiveB
            isoType = Comp a b funType
            in (mapIso,isoType)

mapAccIso :: (Iso,T)
mapAccIso=
        let a = TypeVar 'a'
            b = TypeVar 'b'
            c = TypeVar 'c'
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
