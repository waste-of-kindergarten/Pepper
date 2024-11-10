{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module Machine where 

import Data.List (isSuffixOf)
import Debug.Trace
import System.Environment (getArgs)


data Formula =
    Atom String
    | Not Formula
    | Or Formula Formula
    | And Formula Formula
    | Imply Formula Formula
    | Bottom
    deriving (Eq)

data Associativity = L | R | N

type Priority = Int

class Oprand a where
    associativity :: a -> Associativity
    priority :: a -> Priority

instance Oprand Formula where
  associativity :: Formula -> Associativity
  associativity (Atom _) = N
  associativity (Not _) = N
  associativity (Or _ _) = L
  associativity (And _ _) = L
  associativity (Imply _ _) = R
  associativity Bottom = N
  priority :: Formula -> Priority
  priority Bottom = 0
  priority (Atom p) = 0
  priority (Not _) = 1
  priority (And _ _) = 2
  priority (Or _ _) = 3
  priority (Imply _ _) = 4

formulaGen :: Formula -> String
formulaGen Bottom = "⊥"
formulaGen (Atom p) = p
formulaGen ϕ@(Not t) = "¬ " ++ auxiliaryfunc1 (priority ϕ) (priority t) (formulaGen t)
formulaGen ϕ@(And t1 t2) = auxiliaryfunc2l (associativity ϕ) (priority ϕ) (priority t1) (formulaGen t1)
                                ++ " ∧ " ++
                            auxiliaryfunc2r (associativity ϕ) (priority ϕ) (priority t2) (formulaGen t2)
formulaGen ϕ@(Or t1 t2) =  auxiliaryfunc2l (associativity ϕ) (priority ϕ) (priority t1) (formulaGen t1)
                                ++ " ∨ " ++
                            auxiliaryfunc2r (associativity ϕ) (priority ϕ) (priority t2) (formulaGen t2)
formulaGen ϕ@(Imply t1 t2) = auxiliaryfunc2l (associativity ϕ) (priority ϕ) (priority t1) (formulaGen t1)
                                ++ " → " ++
                            auxiliaryfunc2r (associativity ϕ) (priority ϕ) (priority t2) (formulaGen t2)

auxiliaryfunc1 ::  Priority -> Priority -> (String -> String)
auxiliaryfunc1 n1 n2 =
    if n1 < n2 then \ x -> "(" ++ x ++ ")" else id

auxiliaryfunc2l :: Associativity -> Priority -> Priority -> (String -> String)
auxiliaryfunc2l L n1 n2 =
    if n1 < n2
        then \ x ->"(" ++ x ++ ")"
        else id
auxiliaryfunc2l R n1 n2 =
    if n1 <= n2
        then \ x -> "(" ++ x ++ ")"
        else id

auxiliaryfunc2r :: Associativity -> Priority -> Priority -> (String -> String)
auxiliaryfunc2r R n1 n2 =
    if n1 < n2
        then \ x -> "(" ++ x ++ ")"
        else id
auxiliaryfunc2r L n1 n2 =
    if n1 <= n2
        then \ x -> "(" ++ x ++ ")"
        else id

instance Show Formula where
  show :: Formula -> String
  show ϕ = formulaGen ϕ

formula :: Formula
formula = Imply (Atom "p") (Imply (Or (Atom "p") (Atom "q")) (Atom "r"))

-- Natural Deduction
type Premise = Formula
type Premises = [Formula]
type Conclusion = Formula

data Sequent = Sequent {
    getPremises :: Premises ,
    getConclusion :: Conclusion
    }
    | EmptySequent

instance Show Sequent where
  show :: Sequent -> String
  show (Sequent premises conclusion) = premisesgen premises ++ " ⊢ " ++ show conclusion
    where premisesgen [] = ""
          premisesgen [ϕ] = show ϕ
          premisesgen (ϕ1:ϕ2:ϕs) = show ϕ1 ++ ", " ++ premisesgen (ϕ2:ϕs)
  show EmptySequent = "_⊢_"


and_introduction :: Formula -> Formula -> Formula
and_introduction = And

and_elimination1 :: Formula -> Formula
and_elimination1 (And ϕ ψ) = ϕ
and_elimination1 ϕ = error $ "cannot use ∧ₑ₁ for " ++ show ϕ

and_elimination2 :: Formula -> Formula
and_elimination2 (And ϕ ψ) = ψ
and_elimination2 ϕ = error $ "cannot use ∧ₑ₂ for " ++ show ϕ

double_negation_introduction :: Formula -> Formula
double_negation_introduction ϕ = Not (Not ϕ)

double_negation_elimination :: Formula -> Formula
double_negation_elimination (Not (Not ϕ)) = ϕ
double_negation_elimination ϕ = error $ "cannot use ¬¬ₑ for" ++ show ϕ

implies_elimination :: Formula -> Formula -> Formula
implies_elimination (Imply ϕ2 ψ) ϕ1  = if ϕ1 == ϕ2 then ψ else error $ "cannot use →ₑ for " ++ show (Imply ϕ2 ψ) ++ " and " ++ show ϕ1
implies_elimination ϕ ψ = error $ "cannot use →ₑ for " ++ show ϕ ++ " and " ++ show ψ

implies_introduction :: Formula -> Formula -> Formula
implies_introduction = Imply

modus_tollens :: Formula -> Formula -> Formula
modus_tollens (Imply ϕ ψ1) (Not ψ2) = if ψ1 == ψ2 then Not ϕ else error $ "cannot use MT for " ++ show (Imply ϕ ψ1) ++ " and " ++ show (Not ψ2)
modus_tollens ϕ ψ = error $ "cannot use MT for " ++ show ϕ ++ " and " ++ show ψ

or_introduction1 :: Formula -> Formula -> Formula
or_introduction1 = Or

or_introduction2 :: Formula -> Formula -> Formula
or_introduction2 = flip Or

or_elimination :: Formula -> Formula -> Formula -> Formula -> Formula -> Formula
or_elimination (Or ϕ ψ) ϕ1 η1 ψ1 η2 = if ϕ == ϕ1 && ψ == ψ1 && η1 == η2 then η1 else error $ "cannot use ∨ₑ for " ++ show (Or ϕ ψ)
or_elimination ϕ _ _ _ _ = error $ "cannot use ∨ₑ for " ++ show ϕ

not_elimination :: Formula -> Formula -> Formula
not_elimination ϕ1 (Not ϕ2) = if ϕ1 == ϕ2 then Bottom else error $ "cannot use ¬ₑ for " ++ show ϕ1 ++ " and " ++ show (Not ϕ2)
not_elimination ϕ ψ = error $ "cannot use ¬ₑ for " ++ show ϕ ++ " and " ++ show ψ

not_introduction :: Formula -> Formula
not_introduction = Not

bottom_elimination :: Formula -> Formula
bottom_elimination = id

proof_by_contradiction :: Formula -> Formula
proof_by_contradiction (Not ϕ) = ϕ
proof_by_contradiction ϕ = error $ "cannot use PBC for " ++ show ϕ

law_of_the_excluded_middle :: Formula -> Formula
law_of_the_excluded_middle ϕ = Or ϕ (Not ϕ)

type Rule = String
type Index = Int

data ProofLine = ProofLine {
    getFormula :: Formula ,
    getRule :: Rule ,
    getDomain :: [Int]
}

instance Show ProofLine where
  show :: ProofLine -> String
  show (ProofLine formula rule domain) = replicate (length domain - 1) '|' ++ "\t" ++ show formula ++ "\t" ++ rule


emptyline :: ProofLine
emptyline = ProofLine Bottom ""  []

type ProofLines = [ProofLine] 

instance Show ProofLines where
  show :: ProofLines -> String
  show prooflines = func prooflines 1
    where func (x:xs) n = show n ++ "\t" ++ show x ++ "\n" ++ func xs (n + 1)
          func [] n = ""

newtype State s a = State {runState :: s -> (a,s)} deriving (Functor)

type Proof = State ProofLines Sequent

generateProof :: Proof -> String
generateProof (State f) = let (sequent,zero:prooflines) = f []
    in show sequent ++ "\n" ++ show prooflines

instance Applicative (State s) where
    pure :: a -> State s a
    pure x = State (\s -> (x,s))
    (<*>) :: State s (a -> b) -> State s a -> State s b
    State f <*> State x = State $ \s -> (fst (f s) (fst (x s)),snd (x s))

instance Monad (State s) where
    (>>=) :: State s a -> (a -> State s b) -> State s b
    State x >>= f = State $ \s -> let (v,s') = x s in runState (f v) s'

class Monad m => ProofMonad a m | m -> a where
    proof :: m a
    premise :: Premises -> m a
    copy :: Int -> m a 
    qed :: m a
    new_assume :: Formula -> m a
    assume :: Formula -> m a
    and_intro :: Int -> Int -> m a
    and_elim1 :: Int -> m a
    and_elim2 :: Int -> m a
    nn_intro :: Int -> m a
    nn_elim :: Int -> m a
    imply_intro :: (Int,Int) -> m a
    imply_elim :: Int -> Int -> m a
    mt :: Int -> Int -> m a
    or_intro1 :: Int -> Formula -> m a
    or_intro2 :: Int -> Formula -> m a
    or_elim :: Int -> (Int,Int) -> (Int,Int) -> m a
    not_elim :: Int -> Int -> m a
    not_intro :: (Int,Int) -> m a
    bot_elim :: Int -> Formula -> m a
    pbc :: (Int,Int) -> m a
    lem :: Formula -> m a

instance ProofMonad Sequent (State ProofLines) where
    proof :: State ProofLines Sequent
    proof = State (\s -> (EmptySequent,[emptyline]))
    new_assume :: Formula -> State ProofLines Sequent
    new_assume = \ϕ -> State (\s -> (EmptySequent, s ++ let lastdomain = (getDomain . last) s
                                                            in [ProofLine ϕ "Assumption" (length s: tail lastdomain)]))
    premise :: Premises -> State ProofLines Sequent
    premise = \premises -> State (\s -> (EmptySequent, s ++ ((\t -> ProofLine t "Premise" [1]) <$> premises)))
    copy :: Int -> State ProofLines Sequent 
    copy = \n -> State (\s -> (EmptySequent, s ++ let lastdomain = (getDomain . last) s 
                                                      proofline = s !! n 
                                                      ϕ = getFormula proofline 
                                                      domain = getDomain proofline 
                                                      in [ProofLine ϕ ("Copy " ++ show n) 
                                                            (if domain `isSuffixOf` lastdomain then lastdomain 
                                                                else error "cannot copy on formula outside current scope") ]))
    qed :: State ProofLines Sequent
    qed = State (\s -> let premises = [getFormula premise | premise <- s, getRule premise == "Premise"]
                           lastline = last s
                           conclusion = if getDomain lastline == [1]
                                          then getFormula lastline
                                          else error "cannot qed because boxes are not closed"
                          in (Sequent premises conclusion,s))
    assume :: Formula -> State ProofLines Sequent
    assume = \ϕ -> State (\s -> (EmptySequent, s ++ let lastdomain = (getDomain . last) s
                                                        in [ProofLine ϕ "Assumption" (length s:lastdomain)]))
    and_intro :: Int -> Int -> State ProofLines Sequent
    and_intro = \ m n -> State (\s -> (EmptySequent, let proofline1 = s !! m
                                                         proofline2 = s !! n
                                                         domain1 = getDomain proofline1
                                                         domain2 = getDomain proofline2
                                                         ϕ = getFormula proofline1
                                                         ψ = getFormula proofline2
                                                         lastline = last s
                                                         lastdomain = getDomain lastline
                                                         in s ++ [ProofLine (and_introduction ϕ ψ)
                                                                        ("∧ᵢ " ++ show m ++ "," ++ show n)
                                                                        (if lastdomain `isSuffixOf` domain1 && lastdomain `isSuffixOf` domain2
                                                                            then lastdomain
                                                                            else error "cannot ∧ᵢ on formulas outside current scope")]
                                                       ))
    and_elim1 :: Int -> State ProofLines Sequent
    and_elim1 = \ n -> State (\s -> (EmptySequent, let proofline = s !! n
                                                       domain = getDomain proofline
                                                       ϕ = getFormula proofline
                                                       lastline = last s
                                                       lastdomain = getDomain lastline
                                                       in s ++ [ProofLine (and_elimination1 ϕ)
                                                                    ("∧e₁ " ++ show n)
                                                                    (if domain `isSuffixOf` lastdomain
                                                                        then lastdomain
                                                                        else error "cannot ∧e₁ on formula outside current scope")]
                                                        ))
    and_elim2 :: Int -> State ProofLines Sequent
    and_elim2 = \ n -> State (\s -> (EmptySequent, let proofline = s !! n
                                                       domain = getDomain proofline
                                                       ϕ = getFormula proofline
                                                       lastline = last s
                                                       lastdomain = getDomain lastline
                                                       in s ++ [ProofLine (and_elimination2 ϕ)
                                                                    ("∧e₂ " ++ show n)
                                                                    (if domain `isSuffixOf` lastdomain
                                                                        then lastdomain
                                                                        else error "cannot ∧e₂ on formula outside current scope")]))
    nn_intro :: Int -> State ProofLines Sequent
    nn_intro = \ n -> State (\s -> (EmptySequent, let proofline = s !! n
                                                      domain = getDomain proofline
                                                      ϕ = getFormula proofline
                                                      lastline = last s
                                                      lastdomain = getDomain lastline
                                                      in s ++ [ProofLine (double_negation_introduction ϕ)
                                                                        ("¬¬ᵢ " ++ show n)
                                                                        (if domain `isSuffixOf` lastdomain
                                                                            then lastdomain
                                                                            else error "cannot ¬¬ᵢ on formula outside current scope")]))
    nn_elim :: Int -> State ProofLines Sequent
    nn_elim = \ n -> State (\s -> (EmptySequent, let proofline = s !! n
                                                     domain = getDomain proofline
                                                     ϕ = getFormula proofline
                                                     lastline = last s
                                                     lastdomain = getDomain lastline
                                                     in s ++ [ProofLine (double_negation_elimination ϕ)
                                                                        ("¬¬ᵢ " ++ show n)
                                                                        (if domain `isSuffixOf` lastdomain
                                                                            then lastdomain
                                                                            else error "cannot ¬¬ₑ on formula outside current scope")]))
    imply_intro :: (Int, Int) -> State ProofLines Sequent
    imply_intro = \(m,n) -> State (\s -> (EmptySequent, 
                                                        let proofline1 = s !! m
                                                            domain1 = getDomain proofline1
                                                            ϕ = getFormula proofline1
                                                            proofline2 = s !! n
                                                            domain2 = getDomain proofline2
                                                            ψ = getFormula proofline2
                                                            lastline = last s
                                                            lastdomain = getDomain lastline
                                                            flag = (getDomain (s !! (m - 1)) == tail domain1) &&
                                                                    (if (n + 1) < length s then getDomain (s !! (n + 1)) == domain2 else True)
                                                            in  s ++ [ProofLine (implies_introduction ϕ ψ)
                                                                        ("→ᵢ " ++ show (m,n))
                                                                        (if flag && (domain1 == domain2)
                                                                            then if lastdomain == domain2 then tail lastdomain
                                                                                    else if lastdomain == tail domain2 then lastdomain
                                                                                        else  error "cannot →ᵢ on formulas outside current scope"
                                                                            else  error "cannot →ᵢ on formulas outside current scope")]))
    imply_elim :: Int -> Int -> State ProofLines Sequent
    imply_elim = \m n -> State (\s -> (EmptySequent, let proofline1 = s !! m
                                                         domain1 = getDomain proofline1
                                                         ϕ = getFormula proofline1
                                                         proofline2 = s !! n
                                                         domain2 = getDomain proofline2
                                                         ψ = getFormula proofline2
                                                         lastline = last s
                                                         lastdomain = getDomain lastline
                                                           in s ++ [ProofLine (implies_elimination ϕ ψ)
                                                            ("→ₑ " ++ show m  ++ "," ++ show n)
                                                            (if domain1 `isSuffixOf` lastdomain  && domain2 `isSuffixOf` lastdomain
                                                                then lastdomain
                                                                else  error "cannot →ₑ on formulas outside current scope")]
                                                           ))
    mt :: Int -> Int -> State ProofLines Sequent
    mt = \ m n -> State (\s -> (EmptySequent, let proofline1 = s !! m
                                                  domain1 = getDomain proofline1
                                                  ϕ = getFormula proofline1
                                                  proofline2 = s !! n
                                                  domain2 = getDomain proofline2
                                                  ψ = getFormula proofline2
                                                  lastline = last s
                                                  lastdomain = getDomain lastline
                                                in s ++ [ProofLine (modus_tollens ϕ ψ)
                                                            ("MT " ++ show m ++ "," ++ show n)
                                                            (if domain1 `isSuffixOf` lastdomain && domain2 `isSuffixOf` lastdomain
                                                                then lastdomain
                                                                else error "cannot MT on formulas outside current scope")]))
    or_intro1 :: Int -> Formula -> State ProofLines Sequent
    or_intro1 = \n ϕ -> State (\s -> (EmptySequent, let proofline = s !! n
                                                        domain = getDomain proofline
                                                        ψ = getFormula proofline
                                                        lastline = last s
                                                        lastdomain = getDomain lastline
                                                        in s ++ [ProofLine (or_introduction1 ψ ϕ)
                                                                        ("∨i₁ " ++ show n)
                                                                        (if domain `isSuffixOf` lastdomain
                                                                            then lastdomain
                                                                            else error "cannot ∨i₁ on formula outside current scope")]))
    or_intro2 :: Int -> Formula -> State ProofLines Sequent
    or_intro2 = \n ψ -> State (\s -> (EmptySequent, let proofline = s !! n
                                                        domain = getDomain proofline
                                                        ϕ = getFormula proofline
                                                        lastline = last s
                                                        lastdomain = getDomain lastline
                                                        in s ++ [ProofLine (or_introduction2 ϕ ψ)
                                                                    ("∨i₂ " ++ show n)
                                                                    (if domain `isSuffixOf` lastdomain
                                                                        then lastdomain
                                                                        else error "cannot ∨i₁ on formula outside current scope")]))
    or_elim :: Int -> (Int,Int) -> (Int,Int) -> State ProofLines Sequent
    or_elim = \l (m1,m2) (n1,n2) -> State (\s -> (EmptySequent, let proofline = s !! l
                                                                    domain = getDomain proofline
                                                                    ϕ = getFormula proofline
                                                                    proofline11 = s !! m1
                                                                    domain11 = getDomain proofline11
                                                                    ψ11 = getFormula proofline11
                                                                    proofline12 = s !! m2
                                                                    domain12 = getDomain proofline12
                                                                    ψ12 = getFormula proofline12
                                                                    proofline21 = s !! n1
                                                                    domain21 = getDomain proofline21
                                                                    ψ21 = getFormula proofline21
                                                                    proofline22 = s !! n2
                                                                    domain22 = getDomain proofline22
                                                                    ψ22 = getFormula proofline22
                                                                    lastline = last s
                                                                    lastdomain = getDomain lastline
                                                                    flag =  ((getDomain (s !! (m1 - 1)) == tail domain11) || (tail . getDomain) (s !! (m1 - 1)) == tail domain11 ) &&
                                                                            ((getDomain (s !! (m2 + 1)) == tail domain12) || (tail . getDomain) (s !! (m2 + 1)) == tail domain12) &&
                                                                            ((getDomain (s !! (n1 - 1)) ==  tail domain21) || (tail . getDomain) (s !! (n1 - 1)) == tail domain21) &&
                                                                            (if (n2 + 1) < length s then (getDomain (s !! (n2 + 1)) == tail domain22) || (tail . getDomain) (s !! (n2 + 1)) == tail domain22 else True)
                                                                    in  s ++ [ProofLine (or_elimination ϕ ψ11 ψ12 ψ21 ψ22)
                                                                                ("∨ₑ " ++ show l ++ "," ++ show (m1,m2) ++ "," ++ show (n1,n2))
                                                                                (if flag && domain11 == domain12 &&  domain21 == domain22 && domain11 /= domain21 && tail domain11 == tail domain21 && domain `isSuffixOf` domain11
                                                                                    then if lastdomain == domain22 then tail lastdomain
                                                                                            else if lastdomain == tail domain22 then lastdomain
                                                                                                else error "cannot ∨ₑ on formulas outside current scope"
                                                                                            else error "cannot ∨ₑ on formulas outside current scope")]))
    not_elim :: Int -> Int -> State ProofLines Sequent
    not_elim = \m n -> State (\s -> (EmptySequent, let proofline1 = s !! m
                                                       domain1 = getDomain proofline1
                                                       ϕ = getFormula proofline1
                                                       proofline2 = s !! n
                                                       domain2 = getDomain proofline2
                                                       ψ = getFormula proofline2
                                                       lastline = last s
                                                       lastdomain = getDomain lastline
                                                       in s ++ [ProofLine (not_elimination ϕ ψ)
                                                                        ("¬ₑ " ++ show m ++ "," ++ show n)
                                                                        (if domain1 `isSuffixOf` lastdomain && domain2 `isSuffixOf` lastdomain
                                                                            then lastdomain
                                                                            else error "cannot ¬ₑ on formula outside current scope")]))
    not_intro :: (Int,Int)  -> State ProofLines Sequent
    not_intro = \(m, n) -> State (\s -> (EmptySequent, let  proofline1 = s !! m
                                                            domain1 = getDomain proofline1
                                                            ϕ = getFormula proofline1
                                                            proofline2 = s !! n
                                                            domain2 = getDomain proofline2
                                                            ψ = getFormula proofline2
                                                            lastline = last s
                                                            lastdomain = getDomain lastline
                                                            flag = (getDomain (s !! (m - 1)) == domain1) &&
                                                                    (getDomain (s !! (n + 1)) == domain2)
                                                            in s ++ [ProofLine (not_introduction ϕ)
                                                                        ("¬ᵢ " ++ show m ++ "," ++ show n)
                                                                        (if flag && domain1 == domain2
                                                                            then if lastdomain == domain2 then tail lastdomain
                                                                                    else if lastdomain == tail domain2 then lastdomain
                                                                                        else error "cannot ¬ᵢ on formulas outside current scope"
                                                                            else error "cannot ¬ᵢ on formulas outside current scope")]))
    bot_elim :: Int -> Formula -> State ProofLines Sequent
    bot_elim = \n ϕ -> State (\s -> (EmptySequent, let proofline = s !! n
                                                       domain = getDomain proofline
                                                       ϕ = getFormula proofline
                                                       lastline = last s
                                                       lastdomain = getDomain lastline
                                                       in s ++ [ProofLine (bottom_elimination ϕ)
                                                                        ("⊥ₑ " ++ show n)
                                                                        (if domain `isSuffixOf` lastdomain
                                                                            then lastdomain
                                                                            else error "cannot ⊥ₑ on formulas outside current scope")]))
    pbc :: (Int, Int) -> State ProofLines Sequent
    pbc = \(m,n) -> State (\s -> (EmptySequent, let proofline1 = s !! m
                                                    domain1 = getDomain proofline1
                                                    ϕ = getFormula proofline1
                                                    proofline2 = s !! n
                                                    domain2 = getDomain proofline2
                                                    ψ = getFormula proofline2
                                                    lastline = last s
                                                    lastdomain = getDomain lastline
                                                    flag = (getDomain (s !! (m - 1)) == domain1) &&
                                                            getDomain (s !! (n + 1)) == domain2
                                                    in s ++ [ProofLine (proof_by_contradiction ϕ)
                                                                    ("PBC " ++ show (m,n))
                                                                    (if flag && domain1 == domain2
                                                                        then if lastdomain == domain2 then tail lastdomain
                                                                            else if lastdomain == tail domain2 then lastdomain
                                                                                else error "cannot PBC outside current scope"
                                                                        else error "cannot PBC outside current scope")]))
    lem :: Formula -> State ProofLines Sequent
    lem = \ϕ -> State (\s -> (EmptySequent, s ++  let lastline = last s
                                                      lastdomain = getDomain lastline
                                                      in [ProofLine (law_of_the_excluded_middle ϕ)
                                                            "LEM"
                                                            lastdomain]))

instance Show Proof where
  show :: Proof -> String
  show = generateProof
