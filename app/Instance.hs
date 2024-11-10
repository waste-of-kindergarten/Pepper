module Instance where

import Machine
import LatexGen

p = Atom "p"

q = Atom "q"

r = Atom "r"

premises = [p `Or` q]
conclusion = (p `Imply` q) `Imply` q

sequent = Sequent premises conclusion

example :: Proof -- LatexProof For latex
example =
    foldl1 (>>) pro
    where pro = [proof, premise premises, assume p ,
                assume (p `Imply` q),
                imply_elim 3 2,
                imply_intro (3,4),
                new_assume q ,
                assume (p `Imply` q),
                copy 6,
                imply_intro (7,8),
                or_elim 1 (2,5) (6,9),
                qed]



