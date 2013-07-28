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
  , module Text.ParserCombinators.Class
  , SourcePos(..)
  , Parser
  , getPosition
  , parse
  , parseFromFile
  , maybePosToPos
  ) where

import Text.ParserCombinators.Class
import Text.ParserCombinators.Parsek hiding (parse,parseFromFile,Parser)
import qualified Text.ParserCombinators.Parsek as P
import Data.Bits

newtype Parser a = PP (P.Parser (Char, SourcePos) a)
  deriving (Alternative, Applicative, Monad, Functor, MonadPlus)

instance IsParser Parser where
  type SymbolOf Parser = Char
  satisfy p = PP $ fst <$> satisfy (p . fst)
  look = PP $ (map fst) <$> look 
  label lab (PP p) = PP (label lab p)
  (PP p) <<|> (PP q) = PP (p <<|> q)

getPosition :: Parser SourcePos
getPosition = PP $ (\l -> case l of
                  [] -> EOF 
                  ((_,p):_) -> p) <$> look

parse :: FilePath -> Parser a -> (forall s. ParseMethod s a r) -> String -> ParseResult SourcePos r
parse file (PP p) method s = mapErrR snd $ P.parse p method (zip s (scanl updLoc (initLoc file) s))

parseFromFile :: Parser a -> (forall s. ParseMethod s a r) -> FilePath -> IO (ParseResult SourcePos r)
parseFromFile p method file = parse file p method <$> readFile file

maybePosToPos = maybe EOF id

-------------
-- Locations

data SourcePos = Loc {sourceName :: !FilePath, sourceLine :: !Int, sourceCol :: !Int} | EOF
  deriving (Ord,Eq)

instance Show SourcePos where
   show EOF = "end of file"
   show (Loc f l c) = f ++ ":" ++ show l ++ ":" ++ show c


updLoc :: SourcePos -> Char -> SourcePos
updLoc (Loc f l _) '\n' = Loc f (l+1) 0
updLoc (Loc f l c) '\t' = Loc f l ((c+8) .&. complement 7)
updLoc (Loc f l c) _    = Loc f l (c+1)
updLoc EOF         _    = EOF

initLoc :: FilePath -> SourcePos
initLoc p = Loc p 1 0





