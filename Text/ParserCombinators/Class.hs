{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction #-}

module Text.ParserCombinators.Class where
import Data.Char
import Control.Monad
import Control.Applicative

class (Monad p, Alternative p) => IsParser p where
  type SymbolOf p 
  satisfy :: (SymbolOf p -> Bool) -> p (SymbolOf p)
  look :: p [SymbolOf p]
  label :: String -> p a -> p a
  (<<|>) :: p a -> p a -> p a
  

-------------------------------------------------------------------------
-- derived parsers

infix  2 <?>
infixr 3 <<|>

p <?> s = label s p

pzero = mzero

char c    = satisfy (==c) <?> show [c]
noneOf cs = satisfy (\c -> not (c `elem` cs)) <?> ("none of " ++ cs) 
oneOf cs  = satisfy (\c -> c `elem` cs) <?> ("one of " ++ cs) 

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

anySymbol :: IsParser p => p (SymbolOf p)
anySymbol = satisfy (const True)

string :: (IsParser p, SymbolOf p ~ Char) => String -> p String
string s = forM s char <?> show s

choice ps = foldr (<|>) mzero ps

option x p = p <|> return x

between open close p = do open; x <- p; close; return x

-- repetition

manyGreedy p = do 
  x <- (Just <$> p) <<|> (pure Nothing)
  case x of
    Nothing -> return []
    Just y -> (y:) <$> manyGreedy p

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

munch,munch1 :: IsParser m => (SymbolOf m -> Bool) -> m [SymbolOf m]
munch p = scan =<< look
 where
  scan (c:cs) | p c = do anySymbol; as <- scan cs; return (c:as)
  scan _            = do return []

munch1 p = (:) <$> satisfy p <*> munch p

endOfFile = label "end of file" $ do 
  s <- look
  guard (null s)

