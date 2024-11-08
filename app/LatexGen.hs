{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
module LatexGen where
import Machine
import Data.List(isSuffixOf)
import Debug.Trace (trace)


formulaLatexGen :: Formula -> String
formulaLatexGen Bottom = "\\bot"
formulaLatexGen (Atom p) = p
formulaLatexGen ϕ@(Not t) = "\\neg " ++ auxiliaryfunc1 (priority ϕ) (priority t) (formulaLatexGen t)
formulaLatexGen ϕ@(And t1 t2) = auxiliaryfunc2l (associativity ϕ) (priority ϕ) (priority t1) (formulaLatexGen t1)
                                ++ " \\wedge " ++
                            auxiliaryfunc2r (associativity ϕ) (priority ϕ) (priority t2) (formulaLatexGen t2)
formulaLatexGen ϕ@(Or t1 t2) =  auxiliaryfunc2l (associativity ϕ) (priority ϕ) (priority t1) (formulaLatexGen t1)
                                ++ " \\vee " ++
                            auxiliaryfunc2r (associativity ϕ) (priority ϕ) (priority t2) (formulaLatexGen t2)
formulaLatexGen ϕ@(Imply t1 t2) = auxiliaryfunc2l (associativity ϕ) (priority ϕ) (priority t1) (formulaLatexGen t1)
                                ++ " \\rightarrow " ++
                            auxiliaryfunc2r (associativity ϕ) (priority ϕ) (priority t2) (formulaLatexGen t2)

newtype LatexFormula = LatexFormula Formula

newtype LatexSequent = LatexSequent Sequent

instance Show LatexFormula where
    show :: LatexFormula -> String
    show (LatexFormula ϕ) = formulaLatexGen ϕ

data LatexProofLine = LatexProofLine {
    getFormula' :: LatexFormula,
    getRule' :: Rule,
    getDomain' :: [Int]
}

instance Show LatexProofLine where
    show :: LatexProofLine -> String
    show (LatexProofLine  formula rule domain) = show formula ++ " & " ++ rule

type LatexProofLines = [LatexProofLine]

type LatexProof = State LatexProofLines LatexSequent

emptyline' = LatexProofLine (LatexFormula Bottom) "" []



instance ProofMonad LatexSequent (State LatexProofLines) where
    proof :: State LatexProofLines LatexSequent
    proof = State (\s -> (LatexSequent EmptySequent,[emptyline']))
    copy :: Int -> State LatexProofLines LatexSequent
    copy = \n -> State (\s -> (LatexSequent EmptySequent,s ++ let lastdomain = (getDomain' . last) s
                                                                  proofline = s !! n
                                                                  LatexFormula ϕ = getFormula' proofline
                                                                  domain = getDomain' proofline
                                                                  in [LatexProofLine (LatexFormula ϕ) ("Copy " ++ show n)
                                                                            (if domain `isSuffixOf` lastdomain then lastdomain
                                                                                    else error "cannot copy on formula outside current scope")]))
    new_assume :: Formula -> State LatexProofLines LatexSequent
    new_assume = \ϕ -> State (\s -> (LatexSequent EmptySequent, s ++ let lastdomain = (getDomain' . last) s
                                                            in [LatexProofLine (LatexFormula ϕ) "Assumption" (length s: tail lastdomain)]))
    premise :: Premises -> State LatexProofLines LatexSequent
    premise = \premises -> State (\s -> (LatexSequent EmptySequent, s ++ ((\t -> LatexProofLine (LatexFormula t) "Premise" [1]) <$> premises)))
    qed :: State LatexProofLines LatexSequent
    qed = State (\s -> let  premises = [ formula | (LatexProofLine (LatexFormula formula) rule _) <- s, rule == "Premise"]
                            lastline = last s
                            !conclusion = if getDomain' lastline == [1]
                                            then let LatexFormula c = getFormula' lastline in c
                                            else error "cannot qed because boxes are not closed"
                          in  (LatexSequent (Sequent premises conclusion),s))
    assume :: Formula -> State LatexProofLines LatexSequent
    assume = \ϕ -> State (\s -> (LatexSequent EmptySequent, s ++ let lastdomain = (getDomain' . last) s
                                                        in [LatexProofLine (LatexFormula ϕ) "Assumption" (length s:lastdomain)]))
    and_intro :: Int -> Int -> State LatexProofLines LatexSequent
    and_intro = \ m n -> State (\s -> (LatexSequent EmptySequent, let   latexProofLine1 = s !! m
                                                                        latexProofLine2 = s !! n
                                                                        domain1 = getDomain' latexProofLine1
                                                                        domain2 = getDomain' latexProofLine2
                                                                        (LatexFormula ϕ) = getFormula' latexProofLine1
                                                                        (LatexFormula ψ) = getFormula' latexProofLine2
                                                                        lastline = last s
                                                                        lastdomain = getDomain' lastline
                                                                        in s ++ [LatexProofLine (LatexFormula $ and_introduction ϕ ψ)
                                                                                        ("$\\wedge_i$ " ++ show m ++ "," ++ show n)
                                                                                        (if lastdomain `isSuffixOf` domain1 && lastdomain `isSuffixOf` domain2
                                                                                            then lastdomain
                                                                                            else error "cannot ∧ᵢ on formulas outside current scope")]
                                                                    ))
    and_elim1 :: Int -> State LatexProofLines LatexSequent
    and_elim1 = \ n -> State (\s -> (LatexSequent EmptySequent, let latexProofLine = s !! n
                                                                    domain = getDomain' latexProofLine
                                                                    LatexFormula ϕ = getFormula' latexProofLine
                                                                    lastline = last s
                                                                    lastdomain = getDomain' lastline
                                                                    in s ++ [LatexProofLine (LatexFormula $ and_elimination1 ϕ)
                                                                                    ("$\\wedge_{e1}$ " ++ show n)
                                                                                    (if domain `isSuffixOf` lastdomain
                                                                                        then lastdomain
                                                                                        else error "cannot ∧e₁ on formula outside current scope")]
                                                                        ))
    and_elim2 :: Int -> State LatexProofLines LatexSequent
    and_elim2 = \ n -> State (\s -> (LatexSequent EmptySequent, let latexProofLine = s !! n
                                                                    domain = getDomain' latexProofLine
                                                                    LatexFormula ϕ = getFormula' latexProofLine
                                                                    lastline = last s
                                                                    lastdomain = getDomain' lastline
                                                                    in s ++ [LatexProofLine (LatexFormula $ and_elimination2 ϕ)
                                                                                    ("$\\wedge_{e2}$ " ++ show n)
                                                                                    (if domain `isSuffixOf` lastdomain
                                                                                        then lastdomain
                                                                                        else error "cannot ∧e₂ on formula outside current scope")]))
    nn_intro :: Int -> State LatexProofLines LatexSequent
    nn_intro = \ n -> State (\s -> (LatexSequent EmptySequent, let  latexProofLine = s !! n
                                                                    domain = getDomain' latexProofLine
                                                                    LatexFormula ϕ = getFormula' latexProofLine
                                                                    lastline = last s
                                                                    lastdomain = getDomain' lastline
                                                                    in s ++ [LatexProofLine (LatexFormula $ double_negation_introduction ϕ)
                                                                                        ("$\\neg\\neg_i$ " ++ show n)
                                                                                        (if domain `isSuffixOf` lastdomain
                                                                                            then lastdomain
                                                                                            else error "cannot ¬¬ᵢ on formula outside current scope")]))
    nn_elim :: Int -> State LatexProofLines LatexSequent
    nn_elim = \ n -> State (\s -> (LatexSequent EmptySequent, let   latexProofLine = s !! n
                                                                    domain = getDomain' latexProofLine
                                                                    LatexFormula ϕ = getFormula' latexProofLine
                                                                    lastline = last s
                                                                    lastdomain = getDomain' lastline
                                                                    in s ++ [LatexProofLine (LatexFormula $ double_negation_elimination ϕ)
                                                                                        ("$\\neg\\neg_e$ " ++ show n)
                                                                                        (if domain `isSuffixOf` lastdomain
                                                                                            then lastdomain
                                                                                            else error "cannot ¬¬ₑ on formula outside current scope")]))
    imply_intro :: (Int, Int) -> State LatexProofLines LatexSequent
    imply_intro = \(m,n) -> State (\s -> (LatexSequent EmptySequent, let    latexProofLine1 = s !! m
                                                                            domain1 = getDomain' latexProofLine1
                                                                            LatexFormula ϕ = getFormula' latexProofLine1
                                                                            latexProofLine2 = s !! n
                                                                            domain2 = getDomain' latexProofLine2
                                                                            LatexFormula ψ = getFormula' latexProofLine2
                                                                            lastline = last s
                                                                            lastdomain = getDomain' lastline
                                                                            flag = (getDomain' (s !! (m - 1)) == tail domain1) &&
                                                                                    (if (n + 1) < length s then getDomain' (s !! (n + 1)) == domain2 else True)
                                                                            in s ++ [LatexProofLine (LatexFormula $ implies_introduction ϕ ψ)
                                                                                        ("$\\rightarrow_i$ " ++ show (m,n))
                                                                                        (if flag && domain1 == domain2
                                                                                            then if lastdomain == domain2 then tail lastdomain
                                                                                                    else if lastdomain == tail domain2 then lastdomain
                                                                                                        else error "cannot →ᵢ on formulas outside current scope"
                                                                                            else error "cannot →ᵢ on formulas outside current scope")]))
    imply_elim :: Int -> Int -> State LatexProofLines LatexSequent
    imply_elim = \m n -> State (\s -> (LatexSequent EmptySequent, let   latexProofLine1 = s !! m
                                                                        domain1 = getDomain' latexProofLine1
                                                                        LatexFormula ϕ = getFormula' latexProofLine1
                                                                        latexProofLine2 = s !! n
                                                                        domain2 = getDomain' latexProofLine2
                                                                        LatexFormula ψ = getFormula' latexProofLine2
                                                                        lastline = last s
                                                                        lastdomain = getDomain' lastline
                                                                        in s ++ [LatexProofLine (LatexFormula $ implies_elimination ϕ ψ)
                                                                            ("$\\rightarrow_e$ " ++ show m  ++ "," ++ show n)
                                                                            (if domain1 `isSuffixOf` lastdomain  && domain2 `isSuffixOf` lastdomain
                                                                                then lastdomain
                                                                                else  error "cannot →ₑ on formulas outside current scope")]
                                                                        ))
    mt :: Int -> Int -> State LatexProofLines LatexSequent
    mt = \ m n -> State (\s -> (LatexSequent EmptySequent, let  latexProofLine1 = s !! m
                                                                domain1 = getDomain' latexProofLine1
                                                                LatexFormula ϕ = getFormula' latexProofLine1
                                                                latexProofLine2 = s !! n
                                                                domain2 = getDomain' latexProofLine2
                                                                LatexFormula ψ = getFormula' latexProofLine2
                                                                lastline = last s
                                                                lastdomain = getDomain' lastline
                                                                in s ++ [LatexProofLine (LatexFormula $ modus_tollens ϕ ψ)
                                                                            ("$MT$ " ++ show m ++ "," ++ show n)
                                                                            (if domain1 `isSuffixOf` lastdomain && domain2 `isSuffixOf` lastdomain
                                                                                then lastdomain
                                                                                else error "cannot MT on formulas outside current scope")]))
    or_intro1 :: Int -> Formula -> State LatexProofLines LatexSequent
    or_intro1 = \n ϕ -> State (\s -> (LatexSequent EmptySequent, let    latexProofLine = s !! n
                                                                        domain = getDomain' latexProofLine
                                                                        LatexFormula ψ = getFormula' latexProofLine
                                                                        lastline = last s
                                                                        lastdomain = getDomain' lastline
                                                                        in s ++ [LatexProofLine (LatexFormula $ or_introduction1 ψ ϕ)
                                                                                        ("$\\vee_{i1}$ " ++ show n)
                                                                                        (if domain `isSuffixOf` lastdomain
                                                                                            then lastdomain
                                                                                            else error "cannot ∨i₁ on formula outside current scope")]))
    or_intro2 :: Int -> Formula -> State LatexProofLines LatexSequent
    or_intro2 = \n ψ -> State (\s -> (LatexSequent EmptySequent, let    latexProofLine = s !! n
                                                                        domain = getDomain' latexProofLine
                                                                        LatexFormula ϕ = getFormula' latexProofLine
                                                                        lastline = last s
                                                                        lastdomain = getDomain' lastline
                                                                        in s ++ [LatexProofLine (LatexFormula $ or_introduction2 ϕ ψ)
                                                                                    ("$\\vee_{i2}$ " ++ show n)
                                                                                    (if domain `isSuffixOf` lastdomain
                                                                                        then lastdomain
                                                                                        else error "cannot ∨i₁ on formula outside current scope")]))
    or_elim :: Int -> (Int,Int) -> (Int,Int) -> State LatexProofLines LatexSequent
    or_elim = \l (m1,m2) (n1,n2) -> State (\s -> (LatexSequent EmptySequent, let    latexProofLine = s !! l
                                                                                    domain = getDomain' latexProofLine
                                                                                    LatexFormula ϕ = getFormula' latexProofLine
                                                                                    latexProofLine11 = s !! m1
                                                                                    domain11 = getDomain' latexProofLine11
                                                                                    LatexFormula ψ11 = getFormula' latexProofLine11
                                                                                    latexProofLine12 = s !! m2
                                                                                    domain12 = getDomain' latexProofLine12
                                                                                    LatexFormula ψ12 = getFormula' latexProofLine12
                                                                                    latexProofLine21 = s !! n1
                                                                                    domain21 = getDomain' latexProofLine21
                                                                                    LatexFormula ψ21 = getFormula' latexProofLine21
                                                                                    latexProofLine22 = s !! n2
                                                                                    domain22 = getDomain' latexProofLine22
                                                                                    LatexFormula ψ22 = getFormula' latexProofLine22
                                                                                    lastline = last s
                                                                                    lastdomain = getDomain' lastline
                                                                                    flag =  ((getDomain' (s !! (m1 - 1)) == tail domain11) || (tail . getDomain') (s !! (m1 - 1)) == tail domain11 ) &&
                                                                                            ((getDomain' (s !! (m2 + 1)) == tail domain12) || (tail . getDomain') (s !! (m2 + 1)) == tail domain12) &&
                                                                                            ((getDomain' (s !! (n1 - 1)) ==  tail domain21) || (tail . getDomain') (s !! (n1 - 1)) == tail domain21) &&
                                                                                            (if (n2 + 1) < length s then (getDomain' (s !! (n2 + 1)) == tail domain22) || (tail . getDomain') (s !! (n2 + 1)) == tail domain22 else True)
                                                                                    in s ++ [LatexProofLine (LatexFormula $ or_elimination ϕ ψ11 ψ12 ψ21 ψ22)
                                                                                                ("$\\vee_e$ " ++ show l ++ "," ++ show (m1,m2) ++ "," ++ show (n1,n2))
                                                                                                (if flag && domain11 == domain12 &&  domain21 == domain22 && domain11 /= domain21 && tail domain11 == tail domain21 && domain `isSuffixOf` domain11
                                                                                                    then if lastdomain == domain22 then tail lastdomain
                                                                                                            else if lastdomain == tail domain22 then lastdomain
                                                                                                                else error "cannot ∨ₑ on formulas outside current scope"
                                                                                                            else error "cannot ∨ₑ on formulas outside current scope")]))
    not_elim :: Int -> Int -> State LatexProofLines LatexSequent
    not_elim = \m n -> State (\s -> (LatexSequent EmptySequent, let latexProofLine1 = s !! m
                                                                    domain1 = getDomain' latexProofLine1
                                                                    LatexFormula ϕ = getFormula' latexProofLine1
                                                                    latexProofLine2 = s !! n
                                                                    domain2 = getDomain' latexProofLine2
                                                                    LatexFormula ψ = getFormula' latexProofLine2
                                                                    lastline = last s
                                                                    lastdomain = getDomain' lastline
                                                                    in s ++ [LatexProofLine (LatexFormula $ not_elimination ϕ ψ)
                                                                                        ("$\\neg_e$ " ++ show m ++ "," ++ show n)
                                                                                        (if domain1 `isSuffixOf` lastdomain && domain2 `isSuffixOf` lastdomain
                                                                                            then lastdomain
                                                                                            else error "cannot ¬ₑ on formula outside current scope")]))
    not_intro :: (Int,Int)  -> State LatexProofLines LatexSequent
    not_intro = \(m, n) -> State (\s -> (LatexSequent EmptySequent, let     latexProofLine1 = s !! m
                                                                            domain1 = getDomain' latexProofLine1
                                                                            LatexFormula ϕ = getFormula' latexProofLine1
                                                                            latexProofLine2 = s !! n
                                                                            domain2 = getDomain' latexProofLine2
                                                                            LatexFormula ψ = getFormula' latexProofLine2
                                                                            lastline = last s
                                                                            lastdomain = getDomain' lastline
                                                                            flag = (getDomain' (s !! (m - 1)) == domain1) &&
                                                                                    (getDomain' (s !! (n + 1)) == domain2)
                                                                            in s ++ [LatexProofLine (LatexFormula $ not_introduction ϕ)
                                                                                        ("$\\neg_i$ " ++ show m ++ "," ++ show n)
                                                                                        (if flag && domain1 == domain2
                                                                                            then if lastdomain == domain2 then tail lastdomain
                                                                                                    else if lastdomain == tail domain2 then lastdomain
                                                                                                        else error "cannot ¬ᵢ on formulas outside current scope"
                                                                                            else error "cannot ¬ᵢ on formulas outside current scope")]))
    bot_elim :: Int -> Formula -> State LatexProofLines LatexSequent
    bot_elim = \n ϕ -> State (\s -> (LatexSequent EmptySequent, let latexProofLine = s !! n
                                                                    domain = getDomain' latexProofLine
                                                                    LatexFormula ϕ = getFormula' latexProofLine
                                                                    lastline = last s
                                                                    lastdomain = getDomain' lastline
                                                                    in s ++ [LatexProofLine (LatexFormula $ bottom_elimination ϕ)
                                                                                        ("$\\bot_e$ " ++ show n)
                                                                                        (if domain `isSuffixOf` lastdomain
                                                                                            then lastdomain
                                                                                            else error "cannot ⊥ₑ on formulas outside current scope")]))
    pbc :: (Int, Int) -> State LatexProofLines LatexSequent
    pbc = \(m,n) -> State (\s -> (LatexSequent EmptySequent, let    latexProofLine1 = s !! m
                                                                    domain1 = getDomain' latexProofLine1
                                                                    LatexFormula ϕ = getFormula' latexProofLine1
                                                                    latexProofLine2 = s !! n
                                                                    domain2 = getDomain' latexProofLine2
                                                                    LatexFormula ψ = getFormula' latexProofLine2
                                                                    lastline = last s
                                                                    lastdomain = getDomain' lastline
                                                                    flag = (getDomain' (s !! (m - 1)) == domain1) &&
                                                                            getDomain' (s !! (n + 1)) == domain2
                                                                    in s ++ [LatexProofLine (LatexFormula $ proof_by_contradiction ϕ)
                                                                                    ("$PBC$ " ++ show (m,n))
                                                                                    (if flag && domain1 == domain2
                                                                                        then if lastdomain == domain2 then tail lastdomain
                                                                                            else if lastdomain == tail domain2 then lastdomain
                                                                                                else error "cannot PBC outside current scope"
                                                                                        else error "cannot PBC outside current scope")]))
    lem :: Formula -> State LatexProofLines LatexSequent
    lem = \ϕ -> State (\s -> (LatexSequent EmptySequent, s ++  let  lastline = last s
                                                                    lastdomain = getDomain' lastline
                                                                    in [LatexProofLine (LatexFormula $ law_of_the_excluded_middle ϕ)
                                                                            "$LEM$"
                                                                            lastdomain]))


instance Show LatexProofLines where
    show :: LatexProofLines -> String
    show xs = let depth = case xs of
                                [] -> 0
                                _ -> maximum [length t | (LatexProofLine _ _ t) <- xs]
                                    in "\\begin{logicproof}{" ++ (show $ depth - 1) ++ "}\n" ++
                                        (drop 3 $ func xs 1 [1]) ++ "\n\\end{logicproof}"
                where func (x:xs) n stack
                        | getDomain' x == stack = "\\\\\n" ++ show (getFormula' x) ++ " & " ++ (getRule' x)  ++ func xs (n + 1) stack
                        | getDomain' x == tail stack = "\n\\end{subproof}\n" ++ show (getFormula' x) ++ " & " ++ (getRule' x)  ++ func xs (n + 1) (getDomain' x)
                        | (tail . getDomain') x == stack = "\\\\\n\\begin{subproof}\n" ++ show (getFormula' x) ++ " & " ++ (getRule' x)  ++ func xs (n + 1) (getDomain' x)
                        | (tail . getDomain') x == tail stack = "\n\\end{subproof}\n\\begin{subproof}\n" ++ show (getFormula' x) ++ " & " ++ (getRule' x)  ++ func xs (n + 1) (getDomain' x)
                        | otherwise = error "latex internal error"
                      func [] _ _ = ""

instance Show LatexProof where
    show :: LatexProof -> String
    show  = generateLatexCode

generateLatexCode :: LatexProof -> String
generateLatexCode (State f) = let (_,zero:latexProofLines) = f ([] :: LatexProofLines)
                                in show latexProofLines
