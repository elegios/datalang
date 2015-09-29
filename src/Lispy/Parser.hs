{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

module Lispy.Parser (parseFile, pretty) where

import Lispy.Ast (TagF(..), Location(..), SourceRange(..), SourceLoc(..), nowhere, UnTag(..))
import Lispy.Parser.Data

import Text.Parsec hiding (runParser, newline, token, tokens)
import Data.Text.Lazy (Text)
import Data.List (nub)
import Data.Char (isAlpha, isDigit, isSpace, digitToInt)
import Data.Functor.Foldable (Fix(..), cata)
import Control.Monad (void)
import Control.Monad.Reader (Reader, ask, local, runReader)
import Control.Monad.Trans (lift)
import qualified Data.Text.Lazy.IO as LIO
import qualified Text.PrettyPrint as P

lineComment :: String
lineComment = "//"
multiComment :: (String, String)
multiComment = ("/*", "*/")
identifierStart :: Parser Char
identifierCont :: Parser Char
(identifierStart, identifierCont) =
  ( satisfy $ isAlpha `or` (`elem` "+-/*:-_&|\\<>=?!")
  , satisfy $ isAlpha `or` (`elem` "+-/*:-_&|\\<>=?!") `or` isDigit)
  where
    or f g c = f c || g c

type Parser a = ParsecT Text () (Reader Bool) a

parseFile :: FilePath -> IO (Either ParseError [[Token]])
parseFile path = runParser topParser path <$> LIO.readFile path

runParser :: Parser a -> FilePath -> Text -> Either ParseError a
runParser p path text = flip runReader undefined $ runParserT p () path text

topParser :: Parser [[Token]]
topParser = ignoreNewline True $ whiteSpace >> listHelper "" "" statement <* eof

ignoreNewline :: Bool -> Parser a -> Parser a
ignoreNewline ignore = local $ const ignore

token :: Parser Token
token = literal <|> symbol <|> identifier <|> statements <|> list <|> memberAccess

list :: Parser Token
list = tagPosition (List <$> listHelper "(" ")" token <?> "function call")

statements :: Parser Token
statements = tagPosition (Statements <$> listHelper "{" "}" statement <?> "block")

statement :: Parser [Token]
statement = (ignoreNewline False $ token `sepEndBy` whiteSpace1) <?> "statement"

memberAccess :: Parser Token
memberAccess = tagPosition (MemberAccess <$> listHelper "[" "]" token <?> "member access")

listHelper :: String -> String -> Parser a -> Parser [a]
listHelper start end listItem =
  ignoreNewline True . between (try (string start) >> whiteSpace) (string end) $ listItem `sepEndBy` whiteSpace1

symbol :: Parser Token
symbol = tagPosition (Symbol <$> (char '\'' >> many1 identifierCont <?> "symbol character") <?> "symbol")

identifier :: Parser Token
identifier = tagPosition $ fmap Identifier $ (:) <$> identifierStart <*> many identifierCont

literal :: Parser Token
literal = tagPosition $ LiteralToken <$> ((stringLiteral <?> "string") <|> tupleLiteral <|> number <|> keyword)
  where
    number = labels (either IntLit FloatLit <$> natFloat) ["int", "float"]
    keyword = try $ do
      ident <- (:) <$> identifierStart <*> many identifierCont
      flip labels ["true", "false", "_", "null"] $ case ident of
        "true" -> return $ BoolLit True
        "false" -> return $ BoolLit False
        "_" -> return UndefLit
        "null" -> return NullLit
        _ -> fail ""

tupleLiteral :: Parser (Literal Token)
tupleLiteral = TupleLit <$> listHelper "'(" ")" token <?> "tuple"

tagPosition :: Parser (TokF Token) -> Parser Token
tagPosition p = do
  start <- toLoc <$> getPosition
  res <- p
  end <- toLoc <$> getPosition
  return . Fix $ TagF (res, (origLoc start end))
  where
    toLoc pos = SourceLoc (sourceName pos) (sourceLine pos) (sourceColumn pos)
    origLoc st en = OriginalLoc $ SourceRange st en

newline :: Parser ()
newline = skipMany $ satisfy isSpace

whiteSpace :: Parser ()
whiteSpace = white skipMany

whiteSpace1 :: Parser ()
whiteSpace1 = white skipMany1 <?> "whitespace"

white :: (Parser () -> Parser ()) -> Parser ()
white sk = ask >>= \case
  False -> sk (noNewline <|> oneLine <|> multiLine <?> "")
  True -> sk (void (satisfy isSpace) <|> oneLine <|> multiLine <?> "")
  where
    noNewline = void . satisfy $ \c -> c /= '\n' && isSpace c
    (multiStart, multiEnd) = multiComment
    oneLine :: Parser ()
    oneLine = do
      try $ string lineComment
      skipMany $ satisfy (/= '\n')
    multiLine :: Parser ()
    multiLine = do
      try $ string multiStart
      inMulti
    startEnd = nub (multiStart ++ multiEnd)
    inMulti = void (try $ string multiEnd)
          <|> (multiLine >> inMulti)
          <|> (skipMany1 (noneOf startEnd) >> inMulti)
          <|> (oneOf startEnd >> inMulti)
          <?> "end of comment"

natFloat :: Parser (Either Integer Double)
natFloat = (char '0' >> zeroNum) <|> decimalFloat
  where
    zeroNum = (Left <$> (hexadecimal <|> octal <|> binary))
          <|> decimalFloat
          <|> fractFloat 0
          <|> return (Left 0)
    hexadecimal = char 'x' >> number 16 hexDigit
    decimal = number 10 digit
    octal = char 'o' >> number 8 octDigit
    binary = char 'b' >> number 2 (oneOf "01")
    number base baseDigit = do
      digits <- many1 baseDigit
      let n = foldl (\x d -> base*x + toInteger (digitToInt d)) 0 digits
      seq n $ return n
    decimalFloat = do
      n <- decimal
      Left n `option` fractFloat n
    fractFloat n = Right <$> fractExponent n
    fractExponent n =
        ((\fr ex -> (fromInteger n + fr)*ex)
          <$> fraction
          <*> option 1.0 exponent)
      <|>
        ((fromInteger n *) <$> exponent)
    fraction = do
      char '.'
      foldr op 0.0 <$> many1 digit <?> "fraction"
      where op d f = (f + fromIntegral (digitToInt d))/10.0
    exponent = do
      oneOf "eE"
      power <$> (sign <*> (decimal <?> "exponent"))
      where power e | e < 0     = 1.0 / power (-e)
                    | otherwise = fromInteger (10^e)
    sign = (char '-' >> return negate)
       <|> (char '+' >> return id)
       <|> return id

number base baseDigit = do
  digits <- many1 baseDigit
  let n = foldl (\x d -> base*x + toInteger (digitToInt d)) 0 digits
  seq n $ return n

stringLiteral :: Parser (Literal Token)
stringLiteral = fmap StringLit . between (char '"') (char '"' <?> "end of string")
  $ many stringChar
  where
    stringChar = stringLetter <|> stringEscape <?> "string character"
    stringLetter = satisfy $ (/= '"') `and` (/= '\\') `and` (> '\026') --"
      where and f g c = f c && g c
    stringEscape = char '\\'
      >> (charEsc <|> charNum <|> charAscii <|> charControl <?> "escape code")
    charEsc = choice $ parseEsc <$> escMap
      where parseEsc (c, code) = char c >> return code
    charNum = toEnum . fromInteger <$> (number 10 digit
                                       <|> (char 'o' >> number 8 octDigit)
                                       <|> (char 'x' >> number 16 hexDigit)
                                       <|> (char 'b' >> number 2 (oneOf "01")))
    charAscii = choice $ parseAscii <$> asciiMap
      where parseAscii (asc, code) = try $ string asc >> return code
    charControl = do
      code <- char '^' >> upper
      return . toEnum $ fromEnum code - fromEnum 'A' + 1

    escMap = zip "abfnrtv\\\"\'" "\a\b\f\n\r\t\v\\\"\'"
    asciiMap = zip (ascii3codes ++ ascii2codes) (ascii3 ++ ascii2)

    ascii2codes = ["BS","HT","LF","VT","FF","CR","SO","SI","EM",
                   "FS","GS","RS","US","SP"]
    ascii3codes = ["NUL","SOH","STX","ETX","EOT","ENQ","ACK","BEL",
                   "DLE","DC1","DC2","DC3","DC4","NAK","SYN","ETB",
                   "CAN","SUB","ESC","DEL"]

    ascii2 = ['\BS','\HT','\LF','\VT','\FF','\CR','\SO','\SI',
              '\EM','\FS','\GS','\RS','\US','\SP']
    ascii3 = ['\NUL','\SOH','\STX','\ETX','\EOT','\ENQ','\ACK',
              '\BEL','\DLE','\DC1','\DC2','\DC3','\DC4','\NAK',
              '\SYN','\ETB','\CAN','\SUB','\ESC','\DEL']

