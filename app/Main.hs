module Main where
import Machine 
import Instance 
import LatexGen 
import System.Environment (getArgs)
import Parser 
import Data.List (isSuffixOf)

main :: IO ()
main = do 
    xs <- getArgs
    if length xs == 1 
        then let x = head xs 
                in if ".pepper" `isSuffixOf` x 
                    then do script <- readFile x 
                            print $ exec $ linestoProof script
                    else print "usage : pepper <filename.pepper>"
        else do 
                putStrLn "-----"
                print example
{-
main = do
    putStrLn "-----"
    print example
-}