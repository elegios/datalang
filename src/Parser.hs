{-# LANGUAGE FlexibleContexts #-}

module Parser where

import Ast
import Data.Functor ((<$>), (<$))
import Control.Applicative ((<*>), (<*))
import Control.Monad.Identity
import Text.Parsec hiding (runParser)
import Text.Parsec.Expr
import qualified Data.Text.Lazy as L
import qualified Data.Text.Lazy.IO as LIO
import qualified Data.Map as M
import qualified Text.Parsec.Token as T

type StreamType = L.Text
type StateType = ()
type UnderlyingMonad = Identity

type Parser = ParsecT StreamType StateType UnderlyingMonad

runParser :: Parser a -> StateType -> FilePath -> StreamType -> Either ParseError a
runParser p st path stream = runIdentity $ runParserT p st path stream

langDef :: Stream stream monad Char => T.GenLanguageDef stream state monad
langDef = T.LanguageDef
  { T.commentStart = "/*"
  , T.commentEnd = "*/"
  , T.commentLine = "//"
  , T.nestedComments = True
  , T.caseSensitive = True
  , T.identStart = letter
  , T.identLetter = alphaNum <|> char '_'
  , T.opStart = T.opLetter langDef
  , T.opLetter = oneOf "+-*/%<>=!^&|"
  , T.reservedNames = ["defer", "if", "else", "while", "return", "break", "continue"] -- TODO: all built-in type literals
  , T.reservedOpNames = ["=", "+", "-", "*", "/", "%", "<", ">", "==", "!=", "<=", ">=", ":"] -- TODO: figure out if all these need/should be added, this list is currently incomplete
  }

parseFile :: FilePath -> IO (Either ParseError Source)
parseFile path = runParser sourceParser () path <$> LIO.readFile path

sourceParser :: Parser Source
sourceParser = toSource <$> topParser

toSource :: [Top] -> Source
toSource tops = Source funcDefs typeDefs
  where
    funcDefs = M.fromList [ (n, d) | FunctionDefinition n d <- tops ]
    typeDefs = M.fromList [ (n, d) | TypeDefinition n d <- tops ]

data Top = FunctionDefinition String FuncDef | TypeDefinition String TypeDef

-- TODO: ensure 'try' is used in the right places
topParser :: Parser [Top]
topParser = whiteSpace >> many (identifier >>= \n -> funcDef n <|> typeDef n)
 
funcDef :: String -> Parser Top
funcDef name = FunctionDefinition name <$> def
  where
    def = withPosition $ FuncDef <$> argumentlist <*> argumentlist <*> scope
    argumentlist = parens $ commaSep identifier

statement :: Parser Statement
statement = funcCall
        <|> defer
        <|> shallowCopy
        <|> ifStatement
        <|> while
        <|> scope
        <|> terminator
        <|> varInit

funcCall :: Parser Statement
funcCall = withPosition (try (FuncCall <$> identifier <*> argumentlist) <*> argumentlist) <?> "functioncall"
  where argumentlist = parens $ commaSep expression

defer :: Parser Statement
defer = reserved "defer" >> withPosition (Defer <$> statement) <?> "defer"

shallowCopy :: Parser Statement
shallowCopy = withPosition (ShallowCopy <$> try (expression <* reservedOp "=") <*> expression) <?> "assignment"

ifStatement :: Parser Statement
ifStatement = reserved "if" >> withPosition (If <$> condition <*> thenBody <*> optionMaybe elseBody) <?> "if"
  where
    condition = expression
    thenBody = scope
    elseBody = reserved "else" >> (ifStatement <|> scope)

while :: Parser Statement
while = reserved "while" >> withPosition (While <$> expression <*> scope) <?> "while"

-- TODO: ensure the syntax is unambiguous even without separators, or add separators
-- The 'end statement with linebreak if it can be ended' idea might be doable with
-- some parser state, set by the whiteSpace parser. To look into later
scope :: Parser Statement
scope = (withPosition . braces $ Scope <$> many statement) <?> "scope"

terminator :: Parser Statement
terminator = (withPosition $ Terminator <$> keyword) <?> "terminator"
  where keyword = replace reserved "return" Return <|> replace reserved "break" Break <|> replace reserved "continue" Continue

-- TODO: make varInit a bit better
varInit :: Parser Statement
varInit = withPosition (VarInit <$> identifier <*> (reservedOp ":" >> typeLiteral) <*> return True) <?> "var init"

expression :: Parser Expression
expression = buildExpressionParser expressionTable simpleExpression <?> "expression"

-- TODO: add all operators in here to the reservedOp list
-- TODO: implement all operators, or implement them as something else
expressionTable :: [[Operator StreamType StateType UnderlyingMonad Expression]]
expressionTable =
  [ [prefix "-" AriNegate, prefix "^" AddressOf, prefix "&" Deref, prefix "!" Not]
  , [binary "*" Times, binary "/" Divide, binary "%" Remainder]
  , [binary "+" Plus, binary "-" Minus]
  , [binary "<<" LShift, binary ">>" LogRShift, binary ">>>" AriRShift]
  , [binary "&" BinAnd]
  , [binary "|" BinOr]
  , [binary "<" Lesser, binary ">" Greater, binary "<=" LE, binary ">=" GE, binary "==" Equal, binary "!=" NotEqual]
  , [binary "&&" ShortAnd]
  , [binary "||" ShortOr]
  ]

-- TODO: pretty ugly range here, it only covers the operator, not both expressions and the operator
binary :: String -> BinOp -> Operator StreamType StateType UnderlyingMonad Expression
binary  name op = Infix (withPosition $ (\s e1 e2 -> Bin op e1 e2 s) <$ reservedOp name) AssocLeft

prefix :: String -> UnOp -> Operator StreamType StateType UnderlyingMonad Expression
prefix  name op = Prefix (withPosition $ flip (Un op) <$ reservedOp name)

postfix :: String -> UnOp -> Operator StreamType StateType UnderlyingMonad Expression
postfix name op = Postfix (withPosition $ flip (Un op) <$ reservedOp name)

simpleExpression :: Parser Expression
simpleExpression = (parens expression <|> exprFunc <|> exprLit <|> variable) >>= contOrNo <?> "simple expression"
  where
    contOrNo prev = cont prev <|> return prev
    cont prev = choice $ map ($ prev) [memberAccess, subscript]

variable :: Parser Expression
variable = withPosition $ Variable <$> identifier

memberAccess :: Expression -> Parser Expression
memberAccess expr = withPosition $ dot >> MemberAccess expr <$> identifier

subscript :: Expression -> Parser Expression
subscript expr = withPosition $ Subscript expr <$> brackets expression

-- TODO: infer the returntype of an exprFunc, meaning don't set it here, do it later
exprFunc :: Parser Expression
exprFunc = withPosition $ try (ExprFunc <$> identifier <*> argumentlist) <*> rettype
  where
    argumentlist = parens $ commaSep expression
    rettype = reservedOp ":" >> typeLiteral

exprLit :: Parser Expression
exprLit = withPosition $ ExprLit <$> variants
  where variants = replace reserved "true" (BLit True)
               <|> replace reserved "false" (BLit False)
               <|> numLit

numLit :: Parser Literal
numLit = either ILit FLit <$> naturalOrFloat <*> (reservedOp ":" >> typeLiteral)
          
typeDef :: String -> Parser Top
typeDef name = TypeDefinition name <$> def
  where
    def = withPosition $ TypeDef <$> typeParams <*> (try (reservedOp ":") >> typeLiteral)
    typeParams = option [] . angles $ commaSep1 identifier

typeLiteral :: Parser Type
typeLiteral = simpleTypeLiteral
          <|> namedTypeLiteral
          <|> pointerTypeLiteral
          <|> chunkTypeLiteral
          <|> structTypeLiteral
          
simpleTypeLiteral :: Parser Type
simpleTypeLiteral = uintTypeLiteral <|> remainingParser
  where
    remainingParser = choice . map (uncurry $ replace reserved) $ typePairs
    typePairs = [ ("i8", I8)
                , ("i16", I16)
                , ("i32", I32)
                , ("i64", I64)
                , ("f32", F32)
                , ("f64", F64)
                , ("bool", BoolT)
                ]

uintTypeLiteral :: Parser Type
uintTypeLiteral = choice . map (uncurry $ replace reserved) $ typePairs
  where
    typePairs = [ ("u8", U8)
                , ("u16", U16)
                , ("u32", U32)
                , ("u64", U64)
                ]

namedTypeLiteral :: Parser Type
namedTypeLiteral = NamedT <$> identifier <*> typeParams
  where typeParams = option [] . angles $ commaSep1 typeLiteral

pointerTypeLiteral :: Parser Type
pointerTypeLiteral = reservedOp "^" >> PointerT <$> typeLiteral

chunkTypeLiteral :: Parser Type
chunkTypeLiteral = Memorychunk <$> brackets countType <*> return True <*> typeLiteral
  where countType = option U32 uintTypeLiteral

structTypeLiteral :: Parser Type
structTypeLiteral = braces $ StructT <$> property `sepEndBy` comma
  where property = (,) <$> identifier <*> (reservedOp ":" >> typeLiteral)

withPosition :: Parser (SourceRange -> a) -> Parser a
withPosition p = do
  start <- getPosition
  ret <- p
  ret <$> toSourceRange start <$> getPosition
          
toSourceRange :: SourcePos -> SourcePos -> SourceRange
toSourceRange from to = SourceRange (toLoc from) (toLoc to)
  where toLoc pos = SourceLoc (sourceName pos) (sourceLine pos) (sourceColumn pos)

lexer :: Stream stream monad Char => T.GenTokenParser stream state monad
lexer = T.makeTokenParser langDef

identifier :: Parser String
identifier = T.identifier lexer

reserved :: String -> Parser ()
reserved = T.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = T.reservedOp lexer

naturalOrFloat :: Parser (Either Integer Double)
naturalOrFloat = T.naturalOrFloat lexer

whiteSpace :: Parser ()
whiteSpace = T.whiteSpace lexer

parens :: Parser a -> Parser a
parens = T.parens lexer

braces :: Parser a -> Parser a
braces = T.braces lexer

angles :: Parser a -> Parser a
angles = T.angles lexer

brackets :: Parser a -> Parser a
brackets = T.brackets lexer

commaSep :: Parser a -> Parser [a]
commaSep = T.commaSep lexer

comma :: Parser ()
comma = void $ T.comma lexer

commaSep1 :: Parser a -> Parser [a]
commaSep1 = T.commaSep1 lexer

dot :: Parser ()
dot = void $ char '.'

replace :: Functor f => (a -> f c) -> a -> b -> f b
replace f a b = b <$ f a
