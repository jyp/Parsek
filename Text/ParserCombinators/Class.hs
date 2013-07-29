{-# LANGUAGE TypeFamilies, NoMonomorphismRestriction #-}

module Text.ParserCombinators.Class where
import Data.Char
import Control.Monad hiding (forM)
import Control.Applicative
import Data.Traversable

-- | Parser class
class (Monad p, Alternative p) => IsParser p where
  type SymbolOf p -- ^ Type of symbols processed
  satisfy :: (SymbolOf p -> Bool) -> p (SymbolOf p) -- ^ accept a symbol satisfying a given predicate
  look :: p [SymbolOf p] -- ^ access the stream of symbols from the current point
  label :: String -> p a -> p a -- ^ label the parser
  (<<|>) :: p a -> p a -> p a -- ^ Left-biased choice.
  

-------------------------------------------------------------------------
-- derived parsers

infix  2 <?>
infixr 3 <<|>

-- | Label a parser
(<?>) :: IsParser p => p a -> String -> p a
p <?> s = label s p

char c    = satisfy (==c) <?> show [c]
noneOf cs = satisfy (\c -> not (c `elem` cs)) <?> ("none of " ++ cs) 
oneOf cs  = satisfy (\c -> c `elem` cs) <?> ("one of " ++ cs) 

spaces    = skipMany space     <?> "white space"
space     = satisfy isSpace    <?> "space"
newline   = char '\n'          <?> "new-line"
tab       = char '\t'          <?> "tab"
upper     = satisfy isUpper    <?> "uppercase letter"
lower     = satisfy isLower    <?> "lowercase letter"
alphaNum  = satisfy isAlphaNum <?> "letter or digit"
letter    = satisfy isAlpha    <?> "letter"
digit     = satisfy isDigit    <?> "digit"
hexDigit  = satisfy isHexDigit <?> "hexadecimal digit"
octDigit  = satisfy isOctDigit <?> "octal digit"

anySymbol :: IsParser p => p (SymbolOf p)
anySymbol = satisfy (const True)

string :: (IsParser p, SymbolOf p ~ Char) => String -> p String
string s = forM s char <?> show s

choice :: Alternative f => [f a] -> f a
choice ps = foldr (<|>) empty ps

option :: Alternative f => a -> f a -> f a
option x p = p <|> pure x

between :: Applicative m => m x -> m y -> m a -> m a
between open close p = open *> p <* close

-- repetition
-- | Greedy repetition: match as many occurences as possible of the argument.
manyGreedy :: IsParser m => m a -> m [a]
manyGreedy p = do 
  x <- (Just <$> p) <<|> pure Nothing
  case x of
    Nothing -> return []
    Just y -> (y:) <$> manyGreedy p

skipMany1 p = p *> skipMany p
skipMany  p = let scan = (p *> scan) <|> pure () in scan

sepBy  p sep = sepBy1 p sep <|> pure []
sepBy1 p sep = (:) <$> p <*> many (sep *> p)

count :: Applicative m => Int -> m a -> m [a]
count n p = sequenceA (replicate n p)

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
  scan (c:cs) | p c = (:) <$> anySymbol <*> scan cs
  scan _            = pure []

munch1 p = (:) <$> satisfy p <*> munch p

endOfFile = label "end of file" $ do 
  s <- look
  guard (null s)

