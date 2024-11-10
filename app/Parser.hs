{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
module Parser where
import Machine
import Control.Monad (ap,MonadPlus(..))
import Control.Applicative (Applicative(..),Alternative (empty,(<|>)))
import Data.Char ( isSpace, isDigit )
import GHC.Unicode (isAlpha)
import Data.List (isPrefixOf)
--import Control.Monad.Trans.Identity
import Data.Functor.Identity

newtype Parser a = Parser {unparse :: String -> [(a,String)]} deriving (Functor)

instance Applicative Parser where 
    pure :: a -> Parser a
    pure = return 
    (<*>) :: Parser (a -> b) -> Parser a -> Parser b
    (<*>) = ap

instance Monad Parser where 
    return :: a -> Parser a
    return = \x -> Parser $ \s -> [(x, s)]
    (>>=) :: Parser a -> (a -> Parser b) -> Parser b
    p >>= f = Parser $ \s -> concat [unparse (f a) s' | (a,s') <- unparse p s]
    
instance Alternative Parser where
    empty :: Parser a
    empty = mzero 
    (<|>) :: Parser a -> Parser a -> Parser a
    (<|>) = mplus

instance MonadPlus Parser where 
    mzero :: Parser a
    mzero = Parser (\s -> [])
    mplus :: Parser a -> Parser a -> Parser a
    p `mplus` q = Parser (\s -> unparse p s ++ unparse q s)

item :: Parser Char 
item = Parser (\xs -> case xs of 
                    "" -> [] 
                    (c:cs) -> [(c, cs)])

(+++) :: Parser a -> Parser a -> Parser a 
p +++ q = Parser (\s -> case unparse (p `mplus` q) s of 
                        [] -> [] 
                        (x:xs) -> [x])

sat :: (Char -> Bool) -> Parser Char 
sat p = do 
    c <- item 
    if p c then return c else mzero 

infix 7 ?? 

(??) :: Parser a -> (a -> Bool) -> Parser a 
p ?? test = do 
    b <- p 
    if test b then return b else mzero 

char :: Char -> Parser Char 
char c = sat (c == )

string :: String -> Parser String 
string "" = return "" 
string (c:cs) = do 
    char c 
    string cs 
    return (c:cs)

many :: Parser a -> Parser [a]
many p = many1 p +++ return [] 

many1 :: Parser a -> Parser [a]
many1 p = do 
    a <- p 
    as <- many p 
    return (a:as)

space :: Parser String 
space = many (sat (== ' '))

token :: Parser String -> Parser String 
token p = do 
    a <- p 
    space 
    return a 

symbol :: String -> Parser String 
symbol cs = token (string cs)

ident :: Parser String 
ident = do 
    l <- sat isAlpha 
    lsc <- many (sat (\a -> isAlpha a || isDigit a))
    return (l:lsc)

identif :: Parser String 
identif = token ident   

parseAtom :: Parser Formula 
parseAtom = do 
    symbol "Atom"
    a <- identif 
    return $ Atom a 

parseBottom :: Parser Formula 
parseBottom = do 
    symbol "Bottom"
    return Bottom 

parseBracket :: Parser Formula 
parseBracket = Parser (\s -> let lindex = findl s 0 
                                 rindex = findr s 0 0 
                                 bracket = drop (lindex + 1) . take rindex $ s 
                                 rest = drop (rindex + 1) s 
                                 in [((fst . head) (unparse parseFormula bracket) ,rest)])
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

parseNumber :: Parser Int 
parseNumber = do
    x <- many (sat isDigit)
    return $ read x  

parseNot :: Parser Formula 
parseNot = do 
    space 
    symbol "Not"
    x <- parseBracket 
    return $ Not x 

parseOr :: Parser Formula 
parseOr = do 
    space 
    symbol "Or"
    x <- parseBracket 
    space 
    y <- parseBracket
    return $ Or x y 

parseAnd :: Parser Formula 
parseAnd = do 
    space 
    symbol "And"
    x <- parseBracket
    space 
    y <- parseBracket
    return $ And x y 

parseImply :: Parser Formula 
parseImply = do 
    space 
    symbol "Imply"
    x <- parseBracket
    space 
    y <- parseBracket
    return $ Imply x y

parseFormula :: Parser Formula 
parseFormula = do 
    space 
    parseBottom +++ parseAtom +++ parseNot +++ parseAnd +++ parseOr +++ parseImply 

parseProof :: Parser Proof 
parseProof = do 
    space 
    string "proof"
    return proof 


parsePremise :: Parser Proof 
parsePremise = do 
    space 
    string "premise" 
    x <- parseFormula 
    return $ premise [x]

parseCopy :: Parser Proof 
parseCopy = do 
    space 
    string "copy"
    space 
    x <- parseNumber
    return $ copy x 

parseQed :: Parser Proof 
parseQed = do 
    space 
    string "qed"
    return qed 

parseNewAssume :: Parser Proof 
parseNewAssume = do 
    space 
    string "new_assume"
    space 
    x <- parseFormula 
    return $ new_assume x 

parseAssume :: Parser Proof 
parseAssume = do 
    space 
    string "assume"
    space 
    x <- parseFormula 
    return $ assume x 

parseAndIntro :: Parser Proof 
parseAndIntro = do 
    space 
    string "and_intro"
    space 
    x <- parseNumber 
    space 
    y <- parseNumber
    return $ and_intro x y 

parseAndElim1 :: Parser Proof 
parseAndElim1 = do 
    space 
    string "and_elim1"
    space 
    x <- parseNumber 
    return $ and_elim1 x  

parseAndElim2 :: Parser Proof 
parseAndElim2 = do 
    space 
    string "and_elim2"
    space 
    x <- parseNumber 
    return $ and_elim2 x     

parseNNIntro :: Parser Proof 
parseNNIntro = do 
    space 
    string "nn_intro"
    space 
    x <- parseNumber 
    return $ nn_intro x 

parseNNElim :: Parser Proof 
parseNNElim = do 
    space 
    string "nn_elim"
    space 
    x <- parseNumber 
    return $ nn_elim x 

parseImplyIntro :: Parser Proof 
parseImplyIntro = do 
    space 
    string "imply_intro"
    space 
    x <- parseNumber
    space 
    char '-'
    space 
    y <- parseNumber 
    return $ imply_intro (x,y)

parseImplyElim :: Parser Proof 
parseImplyElim = do 
    space 
    string "imply_elim"
    space 
    x <- parseNumber 
    space 
    y <- parseNumber 
    return $ imply_elim x y 

parseMT :: Parser Proof 
parseMT = do 
    space 
    string "mt"
    space 
    x <- parseNumber 
    space 
    y <- parseNumber 
    return $ mt x y 

parseOrIntro1 :: Parser Proof 
parseOrIntro1 = do 
    space 
    string "or_intro1"
    space 
    x <- parseNumber 
    space 
    y <- parseFormula 
    return $ or_intro1 x y  

parseOrIntro2 :: Parser Proof 
parseOrIntro2 = do 
    space 
    string "or_intro2"
    space 
    x <- parseNumber 
    space 
    y <- parseFormula 
    return $ or_intro2 x y

parseOrElim :: Parser Proof 
parseOrElim = do 
    space 
    string "or_elim"
    space 
    x <- parseNumber 
    space 
    y1 <- parseNumber
    space 
    char '-'
    y2 <- parseNumber 
    space 
    z1 <- parseNumber 
    space 
    char '-'
    space 
    z2 <- parseNumber 
    return $ or_elim x (y1,y2) (z1,z2)

parseNotElim :: Parser Proof 
parseNotElim = do 
    space 
    string "not_elim"
    space 
    x <- parseNumber 
    space 
    y <- parseNumber 
    return $ not_elim x y 

parseNotIntro :: Parser Proof 
parseNotIntro = do 
    space 
    string "not_intro"
    space 
    x <- parseNumber 
    char '-'
    y <- parseNumber 
    return $ not_intro (x,y)

parseBotElim :: Parser Proof 
parseBotElim = do 
    space 
    string "bot_elim"
    space
    x <- parseNumber 
    space 
    y <- parseFormula 
    return $ bot_elim x y 

parsePBC :: Parser Proof 
parsePBC = do 
    space 
    string "pbc"
    space 
    x <- parseNumber 
    space
    char '-'
    space
    y <- parseNumber 
    return $ pbc (x,y)

parseLEM :: Parser Proof 
parseLEM = do 
    space 
    string "lem"
    space 
    x <- parseFormula 
    return $ lem x 

parseLine :: Parser Proof 
parseLine = 
        parseProof +++ 
        parsePremise +++ 
        parseCopy +++ 
        parseQed +++ 
        parseNewAssume +++ 
        parseAssume +++ 
        parseAndIntro +++ 
        parseAndElim1 +++
        parseAndElim2 +++ 
        parseNNIntro +++ 
        parseNNElim +++ 
        parseImplyIntro +++ 
        parseImplyElim +++ 
        parseMT +++ 
        parseOrIntro1 +++ 
        parseOrIntro2 +++ 
        parseOrElim +++ 
        parseNotElim +++
        parseNotIntro +++
        parseBotElim +++ 
        parsePBC +++ 
        parseLEM 

linetoProof :: String -> Proof 
linetoProof s = let x = unparse parseLine s  
                    pf = fst . head $ x 
                in pf 


linestoProof :: String -> [Proof] 
linestoProof s = let ss = lines s 
                     in [ linetoProof s' | s' <- ss]

class  Monad m => Executable m where 
    exec ::  [m a] -> m a  
    exec xs = foldl1 (>>) xs

deriving instance Executable (State s)
