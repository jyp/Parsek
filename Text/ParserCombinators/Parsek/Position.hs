{-# LANGUAGE RankNTypes, TypeFamilies, GeneralizedNewtypeDeriving #-}

-- Module      :  Text.ParserCombinators.Parsek
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

module Text.ParserCombinators.Parsek.Position
  ( module Text.ParserCombinators.Parsek
  , SourcePos(..)
  , PParser
  , getPos
  )
 where

import Text.ParserCombinators.Parsek
import Data.Bits

newtype PParser a = PP (Parser (Char, SourcePos) a)
  deriving (Alternative, Applicative, Monad, Functor)

instance IsParser PParser where
  type SymbolOf PParser = Char
  satisfy pred = PP $ fst <$> satisfy (pred . fst)
  look = PP $ (map fst) <$> look 

getPos :: PParser SourcePos
getPos = PP $ (\l -> case l of
                  [] -> EOF 
                  ((_,p):_) -> p) <$> look

parse' :: FilePath -> PParser a -> (forall s. ParseMethod s a (Maybe s) r) -> String -> ParseResult (Maybe (Char,SourcePos)) r
parse' file (PP p) method s = parse p method (zip s (scanl updLoc (initLoc file) s))


-------------
-- Locations

data SourcePos = Loc {sourceName :: !FilePath, sourceLine :: !Int, sourceCol :: !Int} | EOF

instance Show SourcePos where
   show EOF = "end of file"
   show (Loc f l c) = f ++ ":" ++ show l ++ ":" ++ show c



updLoc (Loc f l c) '\n' = Loc f (l+1) 0
updLoc (Loc f l c) '\t' = Loc f l ((c+8) .&. complement 7)
updLoc (Loc f l c) _    = Loc f l (c+1)
updLoc EOF         _    = EOF

initLoc p = Loc p 1 0




