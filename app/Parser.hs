{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE BangPatterns #-}
module Parser where

import Machine
import Control.Monad (ap,MonadPlus(..))
import Control.Applicative (Alternative (empty,(<|>)))
import Data.Char ( isSpace, isDigit )
import GHC.Unicode (isAlpha)
import Data.List (isPrefixOf)
--import Control.Monad.Trans.Identity
import Data.Functor.Identity
 


newtype ParserT m a = ParserT {unparseT :: String -> [(m a,String)]} deriving (Functor)

instance Monad m => Applicative (ParserT m) where 
  pure :: Applicative m => a -> ParserT m a
  pure x = ParserT $ \s -> [(pure x,s)] 
  (<*>) :: Applicative m => ParserT m (a -> b) -> ParserT m a -> ParserT m b
  (<*>) = ap 

instance Monad m => Monad (ParserT m) where 
  (>>=) :: Monad m => ParserT m a -> (a -> ParserT m b) -> ParserT m b
  p >>= f = ParserT $ \s -> concat [ unparseT (do { a' <- ParserT (\s -> [(a,s)]) ; f a' }) s' | (a,s') <- unparseT p s]

instance Monad m => Alternative (ParserT m) where 
  empty :: ParserT m a 
  empty = mzero
  (<|>) :: ParserT m a -> ParserT m a -> ParserT m a 
  (<|>) = mplus     

instance Monad m => MonadPlus (ParserT m) where 
    mzero :: ParserT m a 
    mzero = ParserT (\s -> [])
    mplus :: ParserT m a -> ParserT m a -> ParserT m a 
    p `mplus` q = ParserT (\s -> unparseT p s ++ unparseT q s) 

item' :: ParserT Identity Char
item' = ParserT (\xs -> case xs of 
            "" -> []
            (c:cs) -> [(Identity c,cs)])

(++++) :: Monad m => ParserT m a -> ParserT m a -> ParserT m a 
p ++++ q = ParserT (\s -> case unparseT (p `mplus` q) s of  
                                [] -> [] 
                                (x:xs) -> [x]) 


sat' :: (Char -> Bool) -> ParserT Identity Char 
sat' p = do 
    c <- item' 
    if p c then  return c else mzero 

infix 7 ??

(??) :: Monad m => ParserT m a -> (a -> Bool) -> ParserT m a
p ?? test = do 
    b <- p 
    if test b then return b else mzero  

char' :: Char -> ParserT Identity Char
char' c = sat' (c ==)

string' :: String -> ParserT Identity String 
string' "" = return "" 
string' (c:cs) = do 
    char' c 
    string' cs 
    return (c:cs)

many' :: Monad m => ParserT m a -> ParserT m [a]
many' p = many1' p ++++ return [] 

many1' :: Monad m => ParserT m a -> ParserT m [a]
many1' p = do 
    a <- p 
    as <- many' p 
    return (a:as)

space' :: ParserT Identity String 
space' = many' (sat' (== ' '))

token' :: ParserT Identity String -> ParserT Identity String 
token' p = do 
    a <- p 
    space' 
    return a 

symbol' :: String -> ParserT Identity String 
symbol' cs = token' (string' cs)

ident' :: ParserT Identity String 
ident' = do 
    l <- sat' isAlpha
    lsc <- many' (sat' (\a -> isAlpha a || isDigit a))
    return (l:lsc)

identif' :: ParserT Identity String 
identif' = token' ident' 

parseAtom' :: ParserT Identity Formula 
parseAtom' = do 
    symbol' "Atom"
    a <- identif' 
    return $ Atom a

parseBottom' :: ParserT Identity Formula 
parseBottom' = do 
    symbol' "Bottom"
    return Bottom 

parseFormula' :: ParserT Identity Formula 
parseFormula' = do 
    space' 
    parseBottom' ++++ parseAtom' ++++ parseNot' ++++ parseAnd' ++++ parseOr' ++++ parseImply' 

parseBracket' :: ParserT Identity Formula 
parseBracket' = ParserT (\s -> let lindex = findl s 0 
                                   rindex = findr s 0 0 
                                   bracket = drop (lindex + 1) . take rindex $ s 
                                   rest = drop (rindex + 1) s 
                                   in [((fst . head) (unparseT parseFormula' bracket) ,rest)])
        where
        findl :: String -> Int -> Int
        findl "" _ = -1
        findl (c:cs) n = if c == '(' then n else findl cs (n + 1)
        findr ::  String -> Int -> Int -> Int
        findr "" _ _ = -1
        findr (c:cs) n p = if c == '('
                            then findr cs (n + 1) (p + 1)
                            else if c == ')'
                                    then if p /= 1 then findr cs (n + 1) (p - 1) else n
                                    else findr cs (n + 1) p                           

parseNumber :: ParserT Identity Int 
parseNumber = do 
    x <- many' (sat' isDigit)
    return $ read x 

parseNot' :: ParserT Identity Formula 
parseNot' = do 
    space' 
    symbol' "Not" 
    x <- parseBracket'
    return $ Not x 

parseOr' :: ParserT Identity Formula 
parseOr' = do 
    space' 
    symbol' "Or" 
    x <- parseBracket' 
    space'
    y <- parseBracket'
    return $ Or x y 

parseAnd' :: ParserT Identity Formula 
parseAnd' = do 
    space' 
    symbol' "And"
    x <- parseBracket' 
    space' 
    y <- parseBracket' 
    return $ And x y 

parseImply' :: ParserT Identity Formula 
parseImply' = do 
    space' 
    symbol' "Imply" 
    x <- parseBracket' 
    space' 
    y <- parseBracket' 
    return $ Imply x y 

parseLine' :: ParserT Identity String 
parseLine' = many' (char' '\n' ++++ char' '\r')

{-

parseProof :: Parser Proof 
parseProof = do 
    space 
    string "proof"
    space
    return $ State (\s -> (EmptySequent,[emptyline]))

parsePremise :: Parser Proof 
parsePremise = do 
    space 
    string "premise"
    space 
    x <- parseFormula
    return $ premise [x]

parseCopy :: Parser Proof 
parseCopy = do 
    space 
    string "copy"
    space 
    x <- parseDigit 
    return $ copy x
     
test :: Parser Proof 
test = do 
    parseProof 

class MonadTrans t where 
    lift :: Monad m => m a -> t m a 

instance MonadTrans ParserT where 
  lift :: Monad m => m a -> ParserT m a
  lift m = ParserT $ \s -> [(m,s)] 

-}

     