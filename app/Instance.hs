module Instance where 

import Machine
import LatexGen

p = Atom "p"

q = Atom "q"

r = Atom "r"

premises = [(p `And` q) `Or` (p `And` r)]
conclusion = p `And` (q `Or` r)

sequent = Sequent premises conclusion

example :: LatexProof
example = do
    proof
    premise premises
    assume (p `And `q)
    and_elim1 2 
    and_elim2 2
    or_intro1 4 r 
    and_intro 3 5
    new_assume (p `And` r)
    and_elim1 7 
    and_elim2 7
    or_intro2 9 q 
    and_intro 8 10
    or_elim 1 (2,6) (7,11)
    qed
