{-# LANGUAGE FlexibleContexts, TupleSections, FlexibleInstances, MultiParamTypeClasses, LambdaCase #-}

module Parser (parseFile) where

import Parser.Ast
import GlobalAst (SourceLoc(..), SourceRange(..), TSize(..), BinOp(..), UnOp(..), TerminatorType(..))
import Data.Functor ((<$>), (<$))
import Data.Char (isLower, isUpper)
import Data.Either (partitionEithers)
import Control.Applicative ((<*>), (<*))
import Control.Monad.Identity
import Text.Parsec hiding (runParser)
import Text.Parsec.Expr
import qualified Data.Text.Lazy as L
import qualified Data.Text.Lazy.IO as LIO
import qualified Text.Parsec.Token as T

data Box a = Box { unBox :: a }

type StreamType = L.Text
type StateType = Box SourcePos
type UnderlyingMonad = Identity

type Parser = ParsecT StreamType StateType UnderlyingMonad

langDef :: Stream StreamType UnderlyingMonad Char => T.GenLanguageDef StreamType StateType UnderlyingMonad
langDef = T.LanguageDef
  { T.commentStart = "/*"
  , T.commentEnd = "*/"
  , T.commentLine = "//"
  , T.nestedComments = True
  , T.caseSensitive = True
  , T.identStart = letter
  , T.identLetter = alphaNum <|> char '_'
  , T.opStart = T.opLetter langDef
  , T.opLetter = oneOf "+-*/%<>=!^&|:,"
  , T.reservedNames = ["defer", "if", "else", "while", "return", "break", "continue", "null", "let", "mut", "func", "proc", "self", "ref", "to"]
  , T.reservedOpNames =
    [ "-", "^", "&", "!", "*"
    , "/", "%", "+", "-", "<<"
    , ">>", ">>>", "|", "<"
    , ">", "<=", ">=", ":", "="
    , "==", "!=", "&&", "||"
    ]
  }

runParser :: Parser a -> StateType -> FilePath -> StreamType -> Either ParseError a
runParser p st path stream = runIdentity $ runParserT p st path stream

parseFile :: FilePath -> IO (Either ParseError SourceFile)
parseFile path = runParser sourceParser err path <$> LIO.readFile path
  where err = Box $ error "Compiler error: haven't parsed anything, thus cannot find the end position of a thing"

sourceParser :: Parser SourceFile
sourceParser = whiteSpace >> SourceFile <$> many (typeDef <* cont) <*> many (callableDef <* cont) <* eof

callableDef :: Parser CallableDef
callableDef = withPosition $
  (reserved "proc" >> cont >> makedef ProcDef commaSep commaSep) <|>
  (reserved "func" >> cont >> makedef FuncDef id id)
  where
    makedef c m1 m2 = c <$> identifier <* cont
                  <*> commaSep typeLiteral <* cont <* symbol "->" <* cont
                  <*> m1 typeLiteral <* cont
                  <*> commaSep identifier <* cont <* symbol "->" <* cont
                  <*> m2 identifier <* cont
                  <*> scope

statement :: Parser Statement
statement = procCall
        <|> defer
        <|> shallowCopy
        <|> ifStatement
        <|> while
        <|> scope
        <|> terminator
        <|> varInit

procCall :: Parser Statement
procCall = withPosition (try (ProcCall <$> expression <* cont <* char '#') <*> is <*> os) <?> "proc call"
  where
    is = whiteSpace >> commaSep expression
    os = option [] $ try (cont >> symbol "#") >> commaSep expression

defer :: Parser Statement
defer = withPosition (reserved "defer" >> cont >> (Defer <$> statement)) <?> "defer"

shallowCopy :: Parser Statement
shallowCopy = withPosition (ShallowCopy <$> try (expression <* cont <* symbol "=") <* cont <*> expression) <?> "assignment"

ifStatement :: Parser Statement
ifStatement = withPosition (reserved "if" >> cont >> If <$> condition <*> thenBody <*> optionMaybe elseBody) <?> "if"
  where
    condition = expression
    thenBody = cont >> scope
    elseBody = try (cont >> reserved "else") >> cont >> (ifStatement <|> scope)

while :: Parser Statement
while = withPosition (reserved "while" >> cont >> While <$> expression <* cont <*> scope) <?> "while"

scope :: Parser Statement
scope = withPosition (Scope <$> braces (statement `sepEndBy` mustCont)) <?> "scope"

terminator :: Parser Statement
terminator = withPosition (Terminator <$> keyword) <?> "terminator"
  where keyword = replace reserved "return" Return <|> replace reserved "break" Break <|> replace reserved "continue" Continue

varInit :: Parser Statement
varInit = withPosition (VarInit <$> (reserved "let" >> cont >> mutable) <* cont <*> identifier <*> typeAnno <*> value) <?> "var init"
  where
    mutable = option False $ replace reserved "mut" True
    typeAnno = optionMaybe $ reservedOp ":" >> cont >> typeLiteral
    value = optionMaybe $ symbol "=" >> cont >> expression

expression :: Parser Expression
expression = buildExpressionParser expressionTable simpleExpression <?> "expression"

-- TODO: implement all operators, or implement them as something else
type ExpOp = Operator StreamType StateType UnderlyingMonad Expression
expressionTable :: [[ExpOp]]
expressionTable =
  [ [post $ choice [funcCall, memberAccess, subscript]]
  , [pre "-" AriNegate, pre "$" Deref, pre "!" Not]
  , [post newTypeConversion]
  , [bin "*" Times, bin "/" Divide, bin "%" Remainder]
  , [bin "+" Plus, bin "-" Minus]
  , [bin "<<" LShift, bin ">>" LogRShift, bin ">>>" AriRShift]
  , [bin "&" BinAnd]
  , [bin "|" BinOr]
  , [post typeAssertion]
  , [bin "<" Lesser, bin ">" Greater, bin "<=" LE, bin ">=" GE, bin "==" Equal, bin "!=" NotEqual]
  , [bin "&&" ShortAnd]
  , [bin "||" ShortOr]
  ]

-- TODO: pretty ugly range here, it only covers the operator, not both expressions and the operator
bin :: String -> BinOp -> ExpOp
bin name op = Infix (withPosition $ (\s e1 e2 -> Bin op e1 e2 s) <$ reservedOp name <* cont) AssocLeft

pre :: String -> UnOp -> ExpOp
pre name op = Prefix (withPosition $ flip (Un op) <$ reservedOp name <* cont)

post :: Parser (Expression -> Expression) -> ExpOp
post p = Postfix . chainl1 p . return $ flip (.)

postHelp :: (e -> i -> SourceRange -> e) -> Parser i -> Parser (e -> e)
postHelp c p = withPosition $ (\i r e -> c e i r) <$> p

newTypeConversion :: Parser (Expression -> Expression)
newTypeConversion =
  postHelp NewTypeConversion $ reserved "to" >> cont >> newTypeName
  where newTypeName = identifier >>= \case
          n@(c:_) | isUpper c -> return n
          n -> unexpected n

funcCall :: Parser (Expression -> Expression)
funcCall = postHelp FuncCall . parens $ commaSep expression

subscript :: Parser (Expression -> Expression)
subscript = postHelp Subscript . brackets . many $
            (Right <$> expression) <|> (Left <$> brOp)

memberAccess :: Parser (Expression -> Expression)
memberAccess = postHelp MemberAccess $ dot >> identifier

typeAssertion :: Parser (Expression -> Expression)
typeAssertion = postHelp TypeAssertion $ reservedOp ":" >> cont >> typeLiteral

simpleExpression :: Parser Expression
simpleExpression = (ref <|> parens expression <|> exprLit <|> variable) <?> "simple expression"
  where
    ref = withPosition $ reserved "ref" >> Un AddressOf <$> parens expression

variable :: Parser Expression
variable = withPosition $ Variable <$> identifier

exprLit :: Parser Expression
exprLit = ExprLit <$> withPosition variants
  where variants = replace reserved "true" (BLit True)
               <|> replace reserved "false" (BLit False)
               <|> replace reserved "null" Null
               <|> replace reserved "_" Undef
               <|> numLit
               <|> structLit

numLit :: Parser (SourceRange -> Literal)
numLit = either ILit FLit <$> naturalOrFloat

structLit :: Parser (SourceRange -> Literal)
structLit = braces $ try lit <|> tupLit
  where
    tupLit = StructTupleLit <$> commaSepEnd expression
    lit = fmap StructLit . commaSepEnd1 $ (,) <$> identifier <* cont <* symbol "=" <*> expression <* cont

typeDef :: Parser TypeDef
typeDef = withPosition $ newType <|> alias
  where
    tParams = option [] . angles $ commaSep1 identifier
    alias = reserved "alias" >> Alias <$> identifier <*> tParams <*> typeLiteral
    newType = do
      constr <- reserved "type" >> NewType <$> identifier <*> tParams
                <* symbol "{" <* cont
                <*> option (HideSome []) (reserved "hide" >> cont >> hidePattern <* cont)
      (ids, brs) <- fmap partitionEithers . many $
                    (Left <$> ((,) <$> identifier <*> replacement <* cont)) <|>
                    (Right <$> ((,) <$> brPattern <*> replacement <* cont))
      symbol "}"
      constr ids brs <$> typeLiteral
    hidePattern = replace symbol "*" HideAll <|> HideSome <$> commaSep1 identifier
    brPattern = brackets . many $
      (BrId <$> identifier <*> optionMaybe (symbol "=" >> expression))
      <|> (BrOp <$> brOp)
    replacement = cont >> (,) <$> optionMaybe (optional (symbol "|" >> cont) >> expression <* cont) <* symbol "->" <* cont <*> expression

typeLiteral :: Parser Type -- TODO: parse func and proc type literals
typeLiteral = simpleTypeLiteral
          <|> namedTypeLiteral
          <|> pointerTypeLiteral
          <|> structTypeLiteral

simpleTypeLiteral :: Parser Type
simpleTypeLiteral = withPosition . choice $ uncurry (replace reserved) <$> typePairs
  where typePairs = [ ("U8",   UIntT  S8)
                    , ("U16",  UIntT  S16)
                    , ("U32",  UIntT  S32)
                    , ("U64",  UIntT  S64)

                    , ("I8",   IntT   S8)
                    , ("I16",  IntT   S16)
                    , ("I32",  IntT   S32)
                    , ("I64",  IntT   S64)

                    , ("F32",  FloatT S32)
                    , ("F64",  FloatT S64)

                    , ("Bool", BoolT)
                    , ("_",    UnknownT)
                    ]

namedTypeLiteral :: Parser Type
namedTypeLiteral = withPosition $ try typeVar <|> (NamedT <$> identifier <*> tParams)
  where
    tParams = option [] . angles $ commaSep1 typeLiteral
    typeVar = do
      n@(c:_) <- identifier
      if isLower c then return $ TypeVar n else fail ""

pointerTypeLiteral :: Parser Type
pointerTypeLiteral = withPosition $ symbol "$" >> PointerT <$> typeLiteral

structTypeLiteral :: Parser Type
structTypeLiteral = withPosition . braces $ StructT <$> commaSepEnd property
  where property = (,) <$> identifier <*> (reservedOp ":" >> typeLiteral)

brOp :: Parser String
brOp = (char '\'' >> many1 letter <* whiteSpace) <|> operator

withPosition :: Parser (SourceRange -> a) -> Parser a
withPosition p = do
  start <- getPosition
  ret <- p
  ret <$> toSourceRange start . unBox <$> getState

toSourceRange :: SourcePos -> SourcePos -> SourceRange
toSourceRange from to = SourceRange (toLoc from) (toLoc to)
  where toLoc pos = SourceLoc (sourceName pos) (sourceLine pos) (sourceColumn pos)

lexer :: Stream StreamType UnderlyingMonad Char => T.GenTokenParser StreamType StateType UnderlyingMonad
lexer = T.makeTokenParser langDef setEndPos

setEndPos :: Parser ()
setEndPos = getPosition >>= putState . Box

symbol :: String -> Parser ()
symbol = void . T.symbol lexer

identifier :: Parser String
identifier = T.identifier lexer

operator :: Parser String
operator = T.operator lexer

reserved :: String -> Parser ()
reserved = T.reserved lexer

reservedOp :: String -> Parser ()
reservedOp = T.reservedOp lexer

naturalOrFloat :: Parser (Either Integer Double)
naturalOrFloat = T.naturalOrFloat lexer

whiteSpace :: Parser ()
whiteSpace = T.whiteSpace lexer

cont :: Parser ()
cont = void . many $ (char '\n' <?> "") >> whiteSpace

mustCont :: Parser ()
mustCont = (void (symbol "\n" <?> "newline") <|> void (T.semi lexer)) >> cont

parens :: Parser a -> Parser a
parens p = symbol "(" >> cont >> p <* cont <* symbol ")"

braces :: Parser a -> Parser a
braces p = symbol "{" >> cont >> p <* cont <* symbol "}"

angles :: Parser a -> Parser a
angles p = symbol "<" >> cont >> p <* cont <* symbol ">"

brackets :: Parser a -> Parser a
brackets p = symbol "[" >> cont >> p <* cont <* symbol "]"

comma :: Parser ()
comma = void $ T.comma lexer

commaSepEnd :: Parser a -> Parser [a]
commaSepEnd p = sepEndBy p $ comma >> cont

commaSepEnd1:: Parser a -> Parser [a]
commaSepEnd1 p = sepEndBy1 p $ comma >> cont

commaSep :: Parser a -> Parser [a]
commaSep p = sepBy p $ comma >> cont

commaSep1 :: Parser a -> Parser [a]
commaSep1 p = sepBy1 p $ comma >> cont

dot :: Parser ()
dot = void $ char '.'

replace :: Functor f => (a -> f c) -> a -> b -> f b
replace f a b = b <$ f a
