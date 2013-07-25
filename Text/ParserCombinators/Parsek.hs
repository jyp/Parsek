{-# LANGUAGE RankNTypes, MultiParamTypeClasses, TypeFamilies, FlexibleContexts #-}
-- |
--
-- Module      :  Parsek
-- Copyright   :  Koen Claessen 2003
-- License     :  GPL
--
-- Maintainer  :  JP Bernardy
-- Stability   :  provisional
-- Portability :  portable
--
-- This module provides the /Parsek/ library developed by Koen Claessen in his
-- functional pearl article /Parallel Parsing Processes/, Journal of Functional
-- Programming, 14(6), 741&#150;757, Cambridge University Press, 2004:
--
-- <http://www.cs.chalmers.se/~koen/pubs/entry-jfp04-parser.html>
--
-- <http://www.cs.chalmers.se/Cs/Grundutb/Kurser/afp/>
--
-- <http://www.cs.chalmers.se/Cs/Grundutb/Kurser/afp/code/week3/Parsek.hs>

module Text.ParserCombinators.Parsek
  -- basic parser type
  ( Parser         -- :: * -> * -> *; Functor, Monad, MonadPlus
  , Expect         -- :: *; = [String]
  , Unexpect       -- :: *; = [String]

  , IsParser (..)
  -- parsers
  , succeeds       -- :: Parser s a -> Parser s (Maybe a)
  , string         -- :: (Eq s, Show s) => [s] -> Parser s [s]

  , char           -- :: Eq s => s -> Parser s s
  , noneOf         -- :: Eq s => [s] -> Parser s s
  , oneOf          -- :: Eq s => [s] -> Parser s s

  , spaces         -- :: Parser Char ()
  , space          -- :: Parser Char Char
  , newline        -- :: Parser Char Char
  , tab            -- :: Parser Char Char
  , upper          -- :: Parser Char Char
  , lower          -- :: Parser Char Char
  , alphaNum       -- :: Parser Char Char
  , letter         -- :: Parser Char Char
  , digit          -- :: Parser Char Char
  , hexDigit       -- :: Parser Char Char
  , octDigit       -- :: Parser Char Char
  , anyChar        -- :: Parser s s
  , anySymbol      -- :: Parser s s
  , munch, munch1  -- :: (s -> Bool) -> Parser s [s]

  -- parser combinators
  , label          -- :: String -> Parser s a -> Parser s a
  , (<?>)          -- :: Parser s a -> String -> Parser s a
  , pzero          -- :: Parser s a
  , (<<|>)         -- :: Parser s a -> Parser s a -> Parser s a
  , choice         -- :: [Parser s a] -> Parser s a
  , option         -- :: a -> Parser s a -> Parser s a
  , between        -- :: Parser s open -> Parser s close -> Parser s a -> Parser s a
  , count          -- :: Int -> Parser s a -> Parser s [a]

  , chainl1        -- :: Parser s a -> Parser s (a -> a -> a) -> Parser s a
  , chainl         -- :: Parser s a -> Parser s (a -> a -> a) -> a -> Parser s a
  , chainr1        -- :: Parser s a -> Parser s (a -> a -> a) -> Parser s a
  , chainr         -- :: Parser s a -> Parser s (a -> a -> a) -> a -> Parser s a

  , skipMany1      -- :: Parser s a -> Parser s ()
  , skipMany       -- :: Parser s a -> Parser s ()
  , sepBy1         -- :: Parser s a -> Parser s sep -> Parser s [a]
  , sepBy          -- :: Parser s a -> Parser s sep -> Parser s [a]

  -- parsing & parse methods
  , ParseMethod    -- :: * -> * -> * -> * -> *
  , ParseResult    -- :: * -> * -> *; = Either (e, Expect, Unexpect) r
  , parseFromFile  -- :: Parser Char a -> ParseMethod Char a e r -> FilePath -> IO (ParseResult e r)
  , parse          -- :: Parser s a -> ParseMethod s a e r -> [s] -> ParseResult e r

  , shortestResult             -- :: ParseMethod s a (Maybe s) a
  , longestResult              -- :: ParseMethod s a (Maybe s) a
  , longestResults             -- :: ParseMethod s a (Maybe s) [a]
  , allResults                 -- :: ParseMethod s a (Maybe s) [a]
  , allResultsStaged           -- :: ParseMethod s a (Maybe s) [[a]]
  , completeResults            -- :: ParseMethod s a (Maybe s) [a]

  , shortestResultWithLeftover -- :: ParseMethod s a (Maybe s) (a,[s])
  , longestResultWithLeftover  -- :: ParseMethod s a (Maybe s) (a,[s])
  , longestResultsWithLeftover -- :: ParseMethod s a (Maybe s) ([a],[s])
  , allResultsWithLeftover     -- :: ParseMethod s a (Maybe s) [(a,[s])]
  
  , module Control.Applicative
  , module Control.Monad
  -- , completeResultsWithLine    -- :: ParseMethod Char a Int [a]
  )
 where

import Control.Applicative
import Control.Monad
  ( MonadPlus(..)
  , forM_
  , guard
  , ap
  )

import Data.List
  ( union
  , intersperse
  )

import Data.Char

infix  2 <?>
infixr 3 <<|>

class (Monad p, Applicative p, Alternative p, Show (SymbolOf p)) => IsParser p where
  type SymbolOf p 
  satisfy :: (SymbolOf p -> Bool) -> p (SymbolOf p)
  look :: p [SymbolOf p]

-------------------------------------------------------------------------
-- type Parser

newtype Parser s a
  = Parser (forall res. (a -> Expect -> P s res) -> Expect -> P s res)

-- type P; parsing processes

data P s res
  = Symbol (s -> P s res)
  | Look ([s] -> P s res)
  | Fail Expect Unexpect
  | Result res (P s res)

-- type Expect, Unexpect

type Expect
  = [String]

type Unexpect
  = [String]

-------------------------------------------------------------------------
-- instances: Functor, Monad, MonadPlus

instance Functor (Parser s) where
  fmap p (Parser f) =
    Parser (\fut -> f (fut . p))

instance Monad (Parser s) where
  return a =
    Parser (\fut -> fut a)

  Parser f >>= k =
    Parser (\fut -> f (\a -> let Parser g = k a in g fut))

  fail s =
    Parser (\fut exp -> Fail exp [s])

instance MonadPlus (Parser s) where
  mzero =
    Parser (\fut exp -> Fail exp [])

  mplus (Parser f) (Parser g) =
    Parser (\fut exp -> f fut exp `plus` g fut exp)

instance Applicative (Parser s) where
  pure = return
  (<*>) = ap

instance Alternative (Parser s) where
  (<|>) = mplus
  empty = mzero

plus :: P s res -> P s res -> P s res
Symbol fut1    `plus` Symbol fut2    = Symbol (\s -> fut1 s `plus` fut2 s)
Fail exp1 err1 `plus` Fail exp2 err2 = Fail (exp1 `union` exp2) (err1 `union` err2)
p              `plus` Result res q   = Result res (p `plus` q)
Result res p   `plus` q              = Result res (p `plus` q)
Look fut1      `plus` Look fut2      = Look (\s -> fut1 s `plus` fut2 s)
Look fut1      `plus` q              = Look (\s -> fut1 s `plus` q)
p              `plus` Look fut2      = Look (\s -> p `plus` fut2 s)
p@(Symbol _)   `plus` _              = p
_              `plus` q@(Symbol _)   = q

-------------------------------------------------------------------------
-- primitive parsers

anySymbol :: IsParser p => p (SymbolOf p)
anySymbol = satisfy (const True)

instance Show s => IsParser (Parser s) where
  type SymbolOf (Parser s) = s
  satisfy pred =
    Parser (\fut exp -> Symbol (\c ->
      if pred c
        then fut c []
        else Fail exp [show [c]] -- FIXME: this is highly doubtful
    ))
  look =
    Parser (\fut exp ->
      Look (\s -> fut s exp)
    )

string s = forM_ s char <?> show s

label :: Parser s a -> String -> Parser s a
label (Parser f) s =
  Parser (\fut exp ->
    if null exp
      then f (\a _ -> fut a []) [s]
      else f fut exp
  )


succeeds :: Parser s a -> Parser s (Maybe a)
succeeds (Parser f) =
  Parser (\fut exp ->
    Look (\xs ->
      let sim (Symbol f)     q (x:xs) = sim (f x) (\k -> Symbol (\_ -> q k)) xs
          sim (Look f)       q xs     = sim (f xs) q xs
          sim p@(Result _ _) q xs     = q (cont p)
          sim _              _ _      = fut Nothing []

          cont (Symbol f)       = Symbol (\x -> cont (f x))
          cont (Look f)         = Look (\s -> cont (f s))
          cont (Result a p)     = fut (Just a) [] `plus` cont p
          cont (Fail exp unexp) = Fail exp unexp

       in sim (f (\a _ -> Result a (Fail [] [])) exp) id xs
    )
  )

-- specialized

-------------------------------------------------------------------------
-- derived parsers

char c    = satisfy (==c)         <?> show [c]
noneOf cs = satisfy (\c -> not (c `elem` cs))
oneOf cs  = satisfy (\c -> c `elem` cs)

spaces    = skipMany space        <?> "white space"
space     = satisfy (isSpace)     <?> "space"
newline   = char '\n'             <?> "new-line"
tab       = char '\t'             <?> "tab"
upper     = satisfy (isUpper)     <?> "uppercase letter"
lower     = satisfy (isLower)     <?> "lowercase letter"
alphaNum  = satisfy (isAlphaNum)  <?> "letter or digit"
letter    = satisfy (isAlpha)     <?> "letter"
digit     = satisfy (isDigit)     <?> "digit"
hexDigit  = satisfy (isHexDigit)  <?> "hexadecimal digit"
octDigit  = satisfy (isOctDigit)  <?> "octal digit"
anyChar   :: IsParser p => p (SymbolOf p)
anyChar   = anySymbol

munch p =
  do cs <- look
     scan cs
 where
  scan (c:cs) | p c = do anySymbol; as <- scan cs; return (c:as)
  scan _            = do return []

munch1 p =
  do c  <- satisfy p
     cs <- munch p
     return (c:cs)

-----------------------------------------------------------
-- parser combinators

(<?>) :: Parser s a -> String -> Parser s a
p <?> s = label p s

pzero :: Parser s a
pzero = mzero

p <<|> q =
  do ma <- succeeds p
     case ma of
       Nothing -> q
       Just a  -> return a

choice ps = foldr (<|>) mzero ps

option x p = p <|> return x

optional p = (do p; return ()) <|> return ()

between open close p = do open; x <- p; close; return x

-- repetition

skipMany1 p = do p; skipMany p
skipMany  p = let scan = (do p; scan) <|> return () in scan

sepBy  p sep = sepBy1 p sep <|> return []
sepBy1 p sep = do x <- p; xs <- many (do sep; p); return (x:xs)

count n p = sequence (replicate n p)

chainr p op x = chainr1 p op <|> return x
chainl p op x = chainl1 p op <|> return x

chainr1 p op = scan
 where
  scan   = do x <- p; rest x
  rest x = (do f <- op; y <- scan; return (f x y)) <|> return x

chainl1 p op = scan
 where
  scan   = do x <- p; rest x
  rest x = (do f <- op; y <- p; rest (f x y)) <|> return x

-------------------------------------------------------------------------
-- type ParseMethod, ParseResult

type ParseMethod s a e r
  = P s a -> [s] -> ParseResult e r

type ParseResult e r
  = Either (e, Expect, Unexpect) r

-- parse functions

parseFromFile :: Parser Char a -> ParseMethod Char a e r -> FilePath -> IO (ParseResult e r)
parseFromFile p method file =
  do s <- readFile file
     return (parse p method s)

parse :: Parser s a -> ParseMethod s a e r -> [s] -> ParseResult e r
parse (Parser f) method xs =
  case method (f (\a exp -> Result a (Fail exp [])) []) xs of
    Left (err, exp, unexp) -> Left (err, [ s | s@(_:_) <- exp ], unexp)
    Right x                -> Right x

-- parse methods

shortestResult :: ParseMethod s a (Maybe s) a
shortestResult p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail [] []) []
  scan (Result res _) _      = Right res
  scan (Fail exp err) (x:xs) = failSym x exp err
  scan (Fail exp err) []     = failEof exp err
  scan (Look f)       xs     = scan (f xs) xs

longestResult :: ParseMethod s a (Maybe s) a
longestResult p xs = scan p Nothing xs
 where
  scan (Symbol sym)   mres       (x:xs) = scan (sym x) mres xs
  scan (Symbol _)     mres       []     = scan (Fail [] []) mres []
  scan (Result res p) _          xs     = scan p (Just res) xs
  scan (Fail exp err) Nothing    (x:xs) = failSym x exp err
  scan (Fail exp err) Nothing    []     = failEof exp err
  scan (Fail _ _)     (Just res) _      = Right res
  scan (Look f)       mres       xs     = scan (f xs) mres xs

longestResults :: ParseMethod s a (Maybe s) [a]
longestResults p xs = scan p [] [] xs
 where
  scan (Symbol sym)   []  old (x:xs) = scan (sym x) [] old xs
  scan (Symbol sym)   new old (x:xs) = scan (sym x) [] new xs
  scan (Symbol _)     new old []     = scan (Fail [] []) new old []
  scan (Result res p) new old xs     = scan p (res:new) [] xs
  scan (Fail exp err) []  []  (x:xs) = failSym x exp err
  scan (Fail exp err) []  []  []     = failEof exp err
  scan (Fail _ _)     []  old _      = Right old
  scan (Fail _ _)     new _   _      = Right new
  scan (Look f)       new old xs     = scan (f xs) new old xs

allResultsStaged :: ParseMethod s a (Maybe s) [[a]]
allResultsStaged p xs = Right (scan p [] xs)
 where
  scan (Symbol sym)   ys (x:xs) = ys : scan (sym x) [] xs
  scan (Symbol _)     ys []     = [ys]
  scan (Result res p) ys xs     = scan p (res:ys) xs
  scan (Fail _ _)     ys _      = [ys]
  scan (Look f)       ys xs     = scan (f xs) ys xs

allResults :: ParseMethod s a (Maybe s) [a]
allResults p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail [] []) []
  scan (Result res p) xs     = Right (res : scan' p xs)
  scan (Fail exp err) (x:xs) = failSym x exp err
  scan (Fail exp err) []     = failEof exp err
  scan (Look f)       xs     = scan (f xs) xs

  scan' p xs =
    case scan p xs of
      Left  _    -> []
      Right ress -> ress

completeResults :: ParseMethod s a (Maybe s) [a]
completeResults p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail [] []) []
  scan (Result res p) []     = Right (res : scan' p [])
  scan (Result _ p)   xs     = scan p xs
  scan (Fail exp err) (x:xs) = failSym x exp err
  scan (Fail exp err) []     = failEof exp err
  scan (Look f)       xs     = scan (f xs) xs

  scan' p xs =
    case scan p xs of
      Left  _    -> []
      Right ress -> ress

-- with left overs

shortestResultWithLeftover :: ParseMethod s a (Maybe s) (a,[s])
shortestResultWithLeftover p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail [] []) []
  scan (Result res _) xs     = Right (res,xs)
  scan (Fail exp err) (x:xs) = failSym x exp err
  scan (Fail exp err) []     = failEof exp err
  scan (Look f)       xs     = scan (f xs) xs

longestResultWithLeftover :: ParseMethod s a (Maybe s) (a,[s])
longestResultWithLeftover p xs = scan p Nothing xs
 where
  scan (Symbol sym)   mres         (x:xs) = scan (sym x) mres xs
  scan (Symbol _)     mres         []     = scan (Fail [] []) mres []
  scan (Result res p) _            xs     = scan p (Just (res,xs)) xs
  scan (Fail exp err) Nothing      (x:xs) = failSym x exp err
  scan (Fail exp err) Nothing      []     = failEof exp err
  scan (Fail _ _)     (Just resxs) _      = Right resxs
  scan (Look f)       mres         xs     = scan (f xs) mres xs

longestResultsWithLeftover :: ParseMethod s a (Maybe s) ([a],Maybe [s])
longestResultsWithLeftover p xs = scan p empty empty xs
 where
  scan (Symbol sym)   ([],_) old    (x:xs) = scan (sym x) empty old xs
  scan (Symbol sym)   new    old    (x:xs) = scan (sym x) empty new xs
  scan (Symbol _)     new    old    []     = scan (Fail [] []) new old []
  scan (Result res p) (as,_) old    xs     = scan p (res:as,Just xs) empty xs
  scan (Fail exp err) ([],_) ([],_) (x:xs) = failSym x exp err
  scan (Fail exp err) ([],_) ([],_) []     = failEof exp err
  scan (Fail _ _)     ([],_)  old _        = Right old
  scan (Fail _ _)     new _   _            = Right new
  scan (Look f)       new    old    xs     = scan (f xs) new old xs

  empty = ([],Nothing)

allResultsWithLeftover :: ParseMethod s a (Maybe s) [(a,[s])]
allResultsWithLeftover p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail [] []) []
  scan (Result res p) xs     = Right ((res,xs) : scan' p xs)
  scan (Fail exp err) (x:xs) = failSym x exp err
  scan (Fail exp err) []     = failEof exp err
  scan (Look f)       xs     = scan (f xs) xs

  scan' p xs =
    case scan p xs of
      Left  _    -> []
      Right ress -> ress
{-
completeResultsWithLine :: ParseMethod Char a Int [a]
completeResultsWithLine p xs = scan p 1 xs
 where
  scan (Symbol sym)   n (x:xs) = let n' = x |> n in n' `seq` scan (sym x) n' xs
  scan (Symbol _)     n []     = scan (Fail [] ["end of file"]) n []
  scan (Result res p) n []     = Right (res : scan' p n [])
  scan (Result _ p)   n xs     = scan p n xs
  scan (Fail exp err) n xs     = Left (n, exp, err)
  scan (Look f)       n xs     = scan (f xs) n xs

  scan' p n xs =
    case scan p n xs of
      Left  _    -> []
      Right ress -> ress

  '\n' |> n = n+1
  _    |> n = n

-- failing
-}
failSym :: s -> Expect -> Unexpect -> ParseResult (Maybe s) r
failSym s exp err = Left (Just s, exp, err)

failEof :: Expect -> Unexpect -> ParseResult (Maybe s) r
failEof exp err = Left (Nothing, exp, err ++ ["end of file"])

-------------------------------------------------------------------------
-- the end.