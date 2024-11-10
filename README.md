A data-level propositional theorem prover using Haskell.

- Check your proof interactively
- Provide readable linear presentation proof
- Auto generate Latex code for assignment

The pepper currently only support Latex code generating within the project. In detail, modify `Instance.hs` and change the type of example into `LatexProof` and `cabal build && cabal run` to compile and execute it. 

In addition, we provide an small interpreter in `Parser.hs` so that the compiled binary file could interprete our proof script named `file.pepper` (eg. `test.pepper`); One could run `cabal run Pepper test.pepper` to see that.
