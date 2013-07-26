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

  , module Text.ParserCombinators.Class
  -- parsers
  , succeeds       -- :: Parser s a -> Parser s (Maybe a)
  , (<<|>)         -- :: Parser s a -> Parser s a -> Parser s a

  -- parsing & parse methods
  , ParseMethod   
  , ParseResult   
  , parseFromFile 
  , parse         

  , shortestResult             
  , longestResult              
  , longestResults             
  , allResults                 
  , allResultsStaged           
  , completeResults            

  , shortestResultWithLeftover 
  , longestResultWithLeftover  
  , longestResultsWithLeftover 
  , allResultsWithLeftover     
  
  , module Control.Applicative
  , module Control.Monad
  -- , completeResultsWithLine    -- :: ParseMethod Char a Int [a]
  )
 where

import Prelude hiding (exp,pred)
import Data.Maybe (listToMaybe)
import Control.Applicative
import Control.Monad
  ( MonadPlus(..)
  , forM_
  , guard
  , ap
  )
import Text.ParserCombinators.Class

import Data.List
  ( union
  , intersperse
  )

import Data.Char

infixr 3 <<|>

-------------------------------------------------------------------------
-- type Parser

newtype Parser s a
  = Parser (forall res. (a -> Expect s -> P s res) -> Expect s -> P s res)

-- type P; parsing processes

data P s res
  = Symbol (s -> P s res)
  | Look ([s] -> P s res)
  | Fail (Err s)
  | Result res (P s res)

type Err s = [(Expect s, -- we expect this stuff
               String -- but failed for this reason
              )]

-- | An intersection (nesting) of things currently expected
type Expect s = [(String, -- Expect this
                  Maybe s -- Here
                )]

-------------------------------------------------------------------------
-- instances: Functor, Monad, MonadPlus

instance Functor (Parser s) where
  fmap p (Parser f) =
    Parser (\fut -> f (fut . p))

instance Monad (Parser s) where
  return a = Parser (\fut -> fut a)

  Parser f >>= k =
    Parser (\fut -> f (\a -> let Parser g = k a in g fut))

  fail s = Parser (\_fut exp -> Fail [(exp,s)])

instance MonadPlus (Parser s) where
  mzero = Parser (\_fut exp -> Fail [(exp,"mzero")])

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
Fail err1      `plus` Fail err2      = Fail (err1 ++ err2)
p              `plus` Result res q   = Result res (p `plus` q)
Result res p   `plus` q              = Result res (p `plus` q)
Look fut1      `plus` Look fut2      = Look (\s -> fut1 s `plus` fut2 s)
Look fut1      `plus` q              = Look (\s -> fut1 s `plus` q)
p              `plus` Look fut2      = Look (\s -> p `plus` fut2 s)
p@(Symbol _)   `plus` _              = p
_              `plus` q@(Symbol _)   = q

-------------------------------------------------------------------------
-- primitive parsers

instance Show s => IsParser (Parser s) where
  type SymbolOf (Parser s) = s
  satisfy pred =
    Parser (\fut exp -> Symbol (\c ->
      if pred c
        then fut c []
        else Fail [(exp,"satisfy")]
    ))
  look =
    Parser (\fut exp ->
      Look (\s -> fut s exp)
    )

  label (Parser f) msg =
    Parser $ \fut exp ->
        Look $ \xs -> 
        f (\a _ -> fut a exp) -- drop the extra expectation in the future
          ((msg,listToMaybe xs):exp) -- locally have an extra expectation


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
          cont (Fail unexp)     = Fail unexp

       in sim (f (\a _ -> Result a (Fail [])) exp) id xs
    )
  )

-----------------------------------------------------------
-- parser combinators

p <<|> q =
  do ma <- succeeds p
     case ma of
       Nothing -> q
       Just a  -> return a

-------------------------------------------------------------------------
-- type ParseMethod, ParseResult

type ParseMethod s a r
  = P s a -> [s] -> ParseResult s r

type ParseResult s r
  = Either (Err s) r

-- parse functions

parseFromFile :: Parser Char a -> ParseMethod Char a r -> FilePath -> IO (ParseResult Char r)
parseFromFile p method file =
  do s <- readFile file
     return (parse p method s)

parse :: Parser s a -> ParseMethod s a r -> [s] -> ParseResult s r
parse (Parser f) method xs = method (f (\a exp -> Result a (Fail [])) []) xs

notEndOfFile = [([("Some symbol",Nothing)],"end of file")]

-- parse methods
shortestResult :: ParseMethod s a a
shortestResult p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail notEndOfFile) []
  scan (Result res _) _      = Right res
  scan (Fail err) _          = Left err 
  scan (Look f)       xs     = scan (f xs) xs

longestResult :: ParseMethod s a a
longestResult p xs = scan p Nothing xs
 where
  scan (Symbol sym)   mres       (x:xs) = scan (sym x) mres xs
  scan (Symbol _)     mres       []     = scan (Fail notEndOfFile) mres []
  scan (Result res p) _          xs     = scan p (Just res) xs
  scan (Fail err)     Nothing    _      = Left err 
  scan (Fail _  )     (Just res) _      = Right res
  scan (Look f)       mres       xs     = scan (f xs) mres xs

longestResults :: ParseMethod s a [a]
longestResults p xs = scan p [] [] xs
 where
  scan (Symbol sym)   []  old (x:xs) = scan (sym x) [] old xs
  scan (Symbol sym)   new old (x:xs) = scan (sym x) [] new xs
  scan (Symbol _)     new old []     = scan (Fail notEndOfFile) new old []
  scan (Result res p) new old xs     = scan p (res:new) [] xs
  scan (Fail err)     []  []  _      = Left err
  scan (Fail _)       []  old _      = Right old
  scan (Fail _)       new _   _      = Right new
  scan (Look f)       new old xs     = scan (f xs) new old xs

allResultsStaged :: ParseMethod s a [[a]]
allResultsStaged p xs = Right (scan p [] xs)
 where
  scan (Symbol sym)   ys (x:xs) = ys : scan (sym x) [] xs
  scan (Symbol _)     ys []     = [ys]
  scan (Result res p) ys xs     = scan p (res:ys) xs
  scan (Fail _)       ys _      = [ys]
  scan (Look f)       ys xs     = scan (f xs) ys xs

allResults :: ParseMethod s a [a]
allResults p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail notEndOfFile) []
  scan (Result res p) xs     = Right (res : scan' p xs)
  scan (Fail err)     _      = Left err
  scan (Look f)       xs     = scan (f xs) xs

  scan' p xs =
    case scan p xs of
      Left  _    -> []
      Right ress -> ress

completeResults :: ParseMethod s a [a]
completeResults p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail notEndOfFile) []
  scan (Result res p) []     = Right (res : scan' p [])
  scan (Result _ p)   xs     = scan p xs
  scan (Fail err)     _      = Left err
  scan (Look f)       xs     = scan (f xs) xs

  scan' p xs =
    case scan p xs of
      Left  _    -> []
      Right ress -> ress

-- with left overs

shortestResultWithLeftover :: ParseMethod s a (a,[s])
shortestResultWithLeftover p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail notEndOfFile) []
  scan (Result res _) xs     = Right (res,xs)
  scan (Fail err)     _      = Left err
  scan (Look f)       xs     = scan (f xs) xs

longestResultWithLeftover :: ParseMethod s a (a,[s])
longestResultWithLeftover p xs = scan p Nothing xs
 where
  scan (Symbol sym)   mres         (x:xs) = scan (sym x) mres xs
  scan (Symbol _)     mres         []     = scan (Fail notEndOfFile) mres []
  scan (Result res p) _            xs     = scan p (Just (res,xs)) xs
  scan (Fail err)     Nothing      _      = Left err
  scan (Fail _)       (Just resxs) _      = Right resxs
  scan (Look f)       mres         xs     = scan (f xs) mres xs

longestResultsWithLeftover :: ParseMethod s a ([a],Maybe [s])
longestResultsWithLeftover p xs = scan p empty empty xs
 where
  scan (Symbol sym)   ([],_) old    (x:xs) = scan (sym x) empty old xs
  scan (Symbol sym)   new    old    (x:xs) = scan (sym x) empty new xs
  scan (Symbol _)     new    old    []     = scan (Fail []) new old []
  scan (Result res p) (as,_) old    xs     = scan p (res:as,Just xs) empty xs
  scan (Fail err)     ([],_) ([],_) _      = Left err
  scan (Fail _)       ([],_)  old _        = Right old
  scan (Fail _)       new _   _            = Right new
  scan (Look f)       new    old    xs     = scan (f xs) new old xs

  empty = ([],Nothing)

allResultsWithLeftover :: ParseMethod s a [(a,[s])]
allResultsWithLeftover p xs = scan p xs
 where
  scan (Symbol sym)   (x:xs) = scan (sym x) xs
  scan (Symbol _)     []     = scan (Fail []) []
  scan (Result res p) xs     = Right ((res,xs) : scan' p xs)
  scan (Fail err)     []     = Left err
  scan (Look f)       xs     = scan (f xs) xs

  scan' p xs =
    case scan p xs of
      Left  _    -> []
      Right ress -> ress
