module AbstractData where


import Data.Number.CReal
import Data.Complex

data A =  One -- 1
        | Sum A B -- a + b
        | Prod A B -- a * b
        | Rec A  -- [a] == 1 + (a * [a]) --Sum One (Prod A (Rec A))
                -- listX == ()|<x,listX> --[] or (x:listX)
                --[] = InjL ();; x:listX = InjR <x,listX>
                -- How to specify the recursive type on Haskell?
                -- Need to make it so [Injl() : Rec a] is valid for the typeChecker
        | TypeVar Char --Allows usage of wildcards on typing rules (Ex: when applying iso to Term, supplied type is only the "output")
        deriving(Eq)
type B = A
-- recA = Sum One (List a))


data T = Iso A B -- a<-->b
        | Comp A B T -- (a<-->b)-->T
        deriving(Eq)
data V =  EmptyV
        | Xval String
        | InjL V
        | InjR V
        | PairV V V
        | Evalue E -- Temporary While I don't evaluate combinations
        deriving(Eq)
-- data CombVals = CVal V
--         | Combination CombVals CombVals
--         | AlphaVal (Alpha Double) CombVals
--         deriving(Eq,Show)
data P =  EmptyP
        | Xprod String --Equivale ao par <(),x>
        | PairP P P
        deriving(Eq)
data E =  Val V
        | LetE P Iso P E
        | Combination E E
        | AlphaVal (Alpha) E
        deriving(Eq)
        --deriving(Eq,Show)
data Iso = Lambda String Iso
        | IsoVar String
        | App Iso Iso
        | Clauses [(V,E)] --(V,CombVals?)
        | Fixpoint String Iso
        deriving(Eq)
data Term = EmptyTerm
        | XTerm String
        | InjLt Term
        | InjRt Term
        | PairTerm Term Term
        | Omega Iso Term
        | Let P Term Term
        -- EXTENSION TERMS
        | CombTerms Term Term
        | AlphaTerm (Alpha) Term
        | ValueT V -- Using it for semantics derivation. (Represents a term that was reduced to a Value)
        deriving(Eq)

data TypeErrors = VarError String String
        | SumError String String
        | ProdError String P
        | IsoError String String String
        | OmegaError String Term
        | AppError String Iso Iso
        | ValueError String V A
        | OrthogonalDecomp String [V]
        | CustomError String String
        | FixpointError String String
        deriving(Show,Eq)

type Alpha = Complex CReal

--data E = Let P Phi P E

type Delta = [(String,A)]
type Psi = [(String,T)]
type OD = [V]
type ODext = [E]

--Not-so-pretty printing.
instance Show (A) where
  show (One) = "1"
  --show (Sum One One) = "Bool"
  show (Sum a b) = show a ++ "+" ++ show b
  show (Prod a b) = show a ++ "*" ++ show b
  show (Rec (Sum one (Prod a recA))) = "[" ++ show a ++ "]"
  show (Rec a) = "[" ++ show a ++ "]"
  show (TypeVar c) = c:[]


instance Show (T) where
  show (Iso a b) = "(" ++ show a ++ "<-->" ++ show b ++ ")"
  show (Comp a b t) = "(" ++ show a ++ "<-->" ++ show b ++ ")" ++ "-->" ++ show t

instance Show (V) where
  show (EmptyV) = "()"
  show (Xval s) = s
  show (InjL v) = "InjL_" ++ show v
  --show (InjR (PairV v1 v2)) = "InjR_[" ++ show v1 ++ " : " ++ show v2 ++ "]"
  show (InjR v) = "InjR_" ++ show v
  show (PairV v1 v2) = "<" ++ show v1 ++ "," ++ show v2 ++ ">"
  show (Evalue e) =  show e

instance Show (E) where
  show (Val v) = show v
  show (LetE p iso p2 e) = "LetE "++show p ++ "="++ show iso ++ " " ++ show p2 ++ "\n\t\tin " ++ show e
  show (Combination v1 v2)
      | show v1 == "" = show v2
      | show v2 == "" = show v1
      | otherwise = show v1 ++ "+" ++ show v2
  show (AlphaVal alpha e)
      | alpha == 0 = "0"
      | alpha == 1 = "" ++ show e
      | imagPart alpha == 0 = capDigitsOnRealNumber 3 alpha ++ "~" ++ show e
      | otherwise = show (alpha) ++ "~" ++ show e


capDigitsOnRealNumber :: Int -> Alpha -> String
capDigitsOnRealNumber 0 (a) = if imagPart a == 0
                              then show (realPart a)
                              else "(" ++ show (realPart a) ++ ":+" ++ show (imagPart a) ++ ")"
capDigitsOnRealNumber i (a) = if imagPart a == 0
                              then showCReal i (realPart a)
                              else "(" ++ showCReal i (realPart a) ++ ":+" ++ show (imagPart a) ++ ")"

instance Show (P) where
  show (EmptyP) = "()"
  show (Xprod s) = s
  show (PairP p1 p2) = "<" ++ show p1 ++ "," ++ show p2 ++ ">"

instance Show (Term) where
  show (EmptyTerm) = "()"
  show (XTerm s) = s
  show (InjLt t) = "InjL_" ++ show t
  show (InjRt (PairTerm t1 t2)) = "InjRt_[" ++ show t1 ++ " : " ++ show t2 ++ "]"
  show (InjRt t) = "InjR_" ++ show t
  show (PairTerm t1 t2) = "<" ++ show t1 ++ "," ++ show t2 ++ ">"
  show (Omega iso t1) = show iso ++ " " ++ show t1
  show (Let p t1 t2) = "let " ++ show p ++ "=" ++ show t1 ++ "\n\tin " ++ show t2
  show (CombTerms t1 t2) = show t1 ++ " + " ++ show t2
  show (AlphaTerm f t) = "(" ++ show f ++ ")" ++ show t
  show (ValueT v) =  show v


instance Show (Iso) where
  show (Lambda s iso) = "Lam  " ++ s ++ ". " ++ show iso
  show (IsoVar s) = s
  show (App iso1 iso2) = show iso1 ++ " " ++ show iso2
  show (Clauses list) = "\n{\n" ++ showPatterns list ++ "}"
  show (Fixpoint f iso) = "Fix " ++ f ++ ". " ++ show iso

showPatterns :: [(V,E)] -> String
showPatterns [] = []
showPatterns (p1:patterns) = show (fst p1) ++ "<-->" ++ show (snd p1) ++ "\n" ++ showPatterns patterns
