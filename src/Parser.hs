{-# LANGUAGE FlexibleContexts, TupleSections, FlexibleInstances, MultiParamTypeClasses, LambdaCase #-}

module Parser (parseFile) where

-- TODO: make whitespace set a flag when it encounters a newline. Make a 'noNewline' parser that uses this. Also a 'wasNewlineOrSemi' for statement separation

import Parser.Ast
import GlobalAst (SourceLoc(..), SourceRange(..), TSize(..), BinOp(..), UnOp(..), TerminatorType(..), Inline(..), location)
import Data.Functor ((<$>), (<$))
import Data.Char (isLower, isUpper)
import Data.Either (partitionEithers)
import Control.Applicative ((<*>), (<*))
import Control.Monad.Identity
import Text.Parsec hiding (runParser, newline)
import Text.Parsec.Expr
import qualified Data.Text.Lazy as L
import qualified Data.Text.Lazy.IO as LIO
import qualified Text.Parsec.Token as T

data ParseState = ParseState { endPos :: SourcePos, wasNewline :: Bool }

type StreamType = L.Text
type StateType = ParseState
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
  , T.reservedNames = ["defer", "if", "else", "while", "return", "break", "continue", "null", "let", "mut", "func", "proc", "self", "ref", "to", "inline", "noinline"]
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
parseFile path = runParser sourceParser initState path <$> LIO.readFile path
  where
    initState = ParseState (error "Compiler error: haven't parsed anything, thus cannot find the end position of a thing") True

sourceParser :: Parser SourceFile
sourceParser = whiteSpace >> SourceFile <$> many typeDef <*> many callableDef <* eof

callableDef :: Parser CallableDef
callableDef = withPosition $
  (reserved "proc" >> makedef ProcDef commaSep commaSep) <|>
  (reserved "func" >> makedef FuncDef id id)
  where
    makedef c m1 m2 = c <$> identifier
                  <*> commaSep typeLiteral <* symbol "->"
                  <*> m1 typeLiteral
                  <*> commaSep identifier <* symbol "->"
                  <*> m2 identifier
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
procCall = withPosition ((spec <|> unspec) <*> is <*> os) <?> "proc call"
  where
    spec = ProcCall
           <$> (replace reserved "inline" AlwaysInline <|>
                replace reserved "noinline" NeverInline)
           <*> expression <* char '#'
    unspec = try (ProcCall UnspecifiedInline <$> expression <* char '#')
    is = whiteSpace >> commaSep expression
    os = option [] $ symbol "#" >> commaSep expression

defer :: Parser Statement
defer = withPosition (reserved "defer" >> (Defer <$> statement)) <?> "defer"

shallowCopy :: Parser Statement
shallowCopy = withPosition (ShallowCopy <$> try (expression <* symbol "=") <*> expression) <?> "assignment"

ifStatement :: Parser Statement
ifStatement = withPosition (reserved "if" >> If <$> condition <*> thenBody <*> optionMaybe elseBody) <?> "if"
  where
    condition = expression
    thenBody = scope
    elseBody = reserved "else" >> (ifStatement <|> scope)

while :: Parser Statement
while = withPosition (reserved "while" >> While <$> expression <*> scope) <?> "while"

scope :: Parser Statement
scope = withPosition (Scope <$> braces (statement `sepEndBy` separator)) <?> "scope"

terminator :: Parser Statement
terminator = withPosition (Terminator <$> keyword) <?> "terminator"
  where keyword = replace reserved "return" Return <|> replace reserved "break" Break <|> replace reserved "continue" Continue

varInit :: Parser Statement
varInit = withPosition (VarInit <$> (reserved "let" >> mutable) <*> identifier <*> typeAnno <*> value) <?> "var init"
  where
    mutable = option False $ replace reserved "mut" True
    typeAnno = optionMaybe $ reservedOp ":" >> typeLiteral
    value = optionMaybe $ symbol "=" >> expression

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
bin name op = Infix (withPosition $ (\s e1 e2 -> Bin op e1 e2 s) <$ reservedOp name) AssocLeft

pre :: String -> UnOp -> ExpOp
pre name op = Prefix (withPosition $ flip (Un op) <$ reservedOp name)

post :: Parser (Expression -> Expression) -> ExpOp
post p = Postfix . chainl1 p . return $ flip (.)

postHelp :: (e -> i -> SourceRange -> e) -> Parser i -> Parser (e -> e)
postHelp c p = withPosition $ (\i r e -> c e i r) <$> p

newTypeConversion :: Parser (Expression -> Expression)
newTypeConversion =
  postHelp NewTypeConversion $ reserved "to" >> newTypeName
  where newTypeName = identifier >>= \case
          n@(c:_) | isUpper c -> return n
          n -> unexpected n

funcCall :: Parser (Expression -> Expression)
funcCall = postHelp (FuncCall UnspecifiedInline) $
           noNewline >> parens (commaSep expression)

subscript :: Parser (Expression -> Expression)
subscript = postHelp Subscript $ noNewline >> (brackets . many $
            (Right <$> expression) <|> (Left <$> brOp))

memberAccess :: Parser (Expression -> Expression)
memberAccess = postHelp MemberAccess $ dot >> identifier

typeAssertion :: Parser (Expression -> Expression)
typeAssertion = postHelp TypeAssertion $ reservedOp ":" >> typeLiteral

simpleExpression :: Parser Expression
simpleExpression = (inlineFuncCall <|> ref <|> parens expression <|> exprLit <|> variable) <?> "simple expression"
  where
    ref = withPosition $ reserved "ref" >> Un AddressOf <$> parens expression

inlineFuncCall :: Parser Expression
inlineFuncCall = withPosition $ do
  constr <- FuncCall <$> inl
  expression >>= \case
    FuncCall _ f is _ -> return $ constr f is
    e -> fail $ "Expected functioncall at " ++ show (location e)
    -- TODO: this fail does not produce a nice error message
  where
    inl = replace reserved "inline" AlwaysInline
      <|> replace reserved "noinline" NeverInline

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
    lit = fmap StructLit . commaSepEnd1 $ (,) <$> identifier <* symbol "=" <*> expression

typeDef :: Parser TypeDef
typeDef = withPosition $ newType <|> alias
  where
    tParams = option [] . angles $ commaSep1 identifier
    alias = reserved "alias" >> Alias <$> identifier <*> tParams <*> typeLiteral
    newType = do
      constr <- reserved "type" >> NewType <$> identifier <*> tParams
                <* symbol "{"
                <*> option (HideSome []) (reserved "hide" >> hidePattern)
      (ids, brs) <- fmap partitionEithers . (`sepEndBy` separator) $
                    (Left <$> ((,) <$> identifier <*> replacement)) <|>
                    (Right <$> ((,) <$> brPattern <*> replacement))
      symbol "}"
      constr ids brs <$> typeLiteral
    hidePattern = replace symbol "*" HideAll <|> HideSome <$> commaSep1 identifier
    brPattern = brackets . many $
      (BrId <$> identifier <*> optionMaybe (symbol "=" >> expression))
      <|> (BrOp <$> brOp)
    replacement = (,) <$> optionMaybe (optional (symbol "|") >> expression) <* symbol "->" <*> expression

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
  ret <$> toSourceRange start . endPos <$> getState

toSourceRange :: SourcePos -> SourcePos -> SourceRange
toSourceRange from to = SourceRange (toLoc from) (toLoc to)
  where toLoc pos = SourceLoc (sourceName pos) (sourceLine pos) (sourceColumn pos)

lexer :: Stream StreamType UnderlyingMonad Char => T.GenTokenParser StreamType StateType UnderlyingMonad
lexer = T.makeTokenParser langDef setEndPos setWasNewline

setEndPos :: Parser ()
setEndPos = getPosition >>= \p -> modifyState (\s -> s { endPos = p})

setWasNewline :: Bool -> Parser ()
setWasNewline n = modifyState $ \s -> s { wasNewline = n }

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

parens :: Parser a -> Parser a
parens = T.parens lexer

braces :: Parser a -> Parser a
braces = T.braces lexer

angles :: Parser a -> Parser a
angles = T.angles lexer

brackets :: Parser a -> Parser a
brackets = T.brackets lexer

comma :: Parser ()
comma = void $ T.comma lexer

commaSepEnd :: Parser a -> Parser [a]
commaSepEnd p = sepEndBy p comma

commaSepEnd1:: Parser a -> Parser [a]
commaSepEnd1 p = sepEndBy1 p comma

commaSep :: Parser a -> Parser [a]
commaSep p = sepBy p comma

commaSep1 :: Parser a -> Parser [a]
commaSep1 p = sepBy1 p comma

dot :: Parser ()
dot = void $ char '.'

replace :: Functor f => (a -> f c) -> a -> b -> f b
replace f a b = b <$ f a

separator :: Parser ()
separator = newline <|> (void . many1 . T.semi) lexer

newline :: Parser ()
newline = getState >>= boolean (return ()) (fail "") . wasNewline <?> "newline"

noNewline :: Parser ()
noNewline = getState >>= boolean (fail "") (return ()) . wasNewline

boolean :: a -> a -> Bool -> a
boolean a b cond = if cond then a else b
