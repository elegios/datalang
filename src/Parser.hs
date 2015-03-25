{-# LANGUAGE FlexibleContexts, TupleSections #-}

module Parser
( parseFile
, SourceFile(..)
, TypeDef(..)
, Source
, BracketToken(..)
, CallableDef(..)
, Type(..)
, Restriction(..)
, NumSpec(..)
, Statement(..)
, Expression(..)
, Literal(..)
) where

import Ast (SourceLoc(..), SourceRange(..), TSize(..), BinOp(..), UnOp(..), TerminatorType(..))
import Data.Functor ((<$>), (<$))
import Data.Char (isLower)
import Control.Applicative ((<*>), (<*))
import Control.Monad.Identity
import Text.Parsec hiding (runParser)
import Text.Parsec.Expr
import qualified Data.Text.Lazy as L
import qualified Data.Text.Lazy.IO as LIO
import qualified Text.Parsec.Token as T

type StreamType = L.Text
type StateType = ()
type UnderlyingMonad = Identity

type Parser = ParsecT StreamType StateType UnderlyingMonad

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
  , T.opLetter = oneOf "+-*/%<>=!^&|:,"
  , T.reservedNames = ["defer", "if", "else", "while", "return", "break", "continue", "null", "let", "mut", "func", "proc", "self", "ref"]
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
parseFile path = runParser sourceParser () path <$> LIO.readFile path

sourceParser :: Parser SourceFile
sourceParser = whiteSpace >> SourceFile <$> many typeDef <*> many callableDef <* eof

callableDef :: Parser CallableDef
callableDef = withPosition $
  (reserved "proc" >> makedef ProcDef commaSep commaSep) <|>
  (reserved "func" >> makedef FuncDef id id)
  where
    makedef c m1 m2 = c
                  <$> restrs
                  <*> commaSep typeLiteral <* reservedOp "->"
                  <*> m1 typeLiteral
                  <*> commaSep identifier <* reservedOp "->"
                  <*> m2 identifier
                  <*> scope
    restrs = option [] . braces $ many restriction

restriction :: Parser (String, Restriction)
restriction = (,) <$> identifier <*> (numR <|> uintR <|> propertiesR)
  where
    numR = replace reserved "num" (NumR NoSpec)
       <|> replace reserved "int" (NumR IntSpec)
       <|> replace reserved "float" (NumR FloatSpec)
    uintR = replace reserved "uint" UIntR
    propertiesR = (\(StructT ps _) -> PropertiesR ps) <$> structTypeLiteral <*> return []

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
procCall = withPosition (try (ProcCall <$> identifier <*> argumentlist) <*> argumentlist) <?> "procedurecall"
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
-- TODO: same operator can be both prefix and infix, causes ambiguousness
scope :: Parser Statement
scope = (withPosition . braces $ Scope <$> many statement) <?> "scope"

terminator :: Parser Statement
terminator = withPosition (Terminator <$> keyword) <?> "terminator"
  where keyword = replace reserved "return" Return <|> replace reserved "break" Break <|> replace reserved "continue" Continue

varInit :: Parser Statement
varInit = withPosition (VarInit <$> (reserved "let" >> mutable) <*> identifier <*> typeAnno <*> value) <?> "var init"
  where
    mutable = option False $ replace reserved "mut" True
    typeAnno = optionMaybe $ reservedOp ":" >> typeLiteral
    value = optionMaybe $ reservedOp "=" >> expression

expression :: Parser Expression
expression = buildExpressionParser expressionTable simpleExpression <?> "expression"

-- TODO: implement all operators, or implement them as something else
expressionTable :: [[Operator StreamType StateType UnderlyingMonad Expression]]
expressionTable =
  [ [pre "-" AriNegate, pre "$" Deref, pre "!" Not]
  , [bin "*" Times, bin "/" Divide, bin "%" Remainder]
  , [bin "+" Plus, bin "-" Minus]
  , [bin "<<" LShift, bin ">>" LogRShift, bin ">>>" AriRShift]
  , [bin "&" BinAnd]
  , [bin "|" BinOr]
  , [typeAssertion]
  , [bin "<" Lesser, bin ">" Greater, bin "<=" LE, bin ">=" GE, bin "==" Equal, bin "!=" NotEqual]
  , [bin "&&" ShortAnd]
  , [bin "||" ShortOr]
  ]

-- TODO: pretty ugly range here, it only covers the operator, not both expressions and the operator
bin :: String -> BinOp -> Operator StreamType StateType UnderlyingMonad Expression
bin  name op = Infix (withPosition $ (\s e1 e2 -> Bin op e1 e2 s) <$ reservedOp name) AssocLeft

pre :: String -> UnOp -> Operator StreamType StateType UnderlyingMonad Expression
pre name op = Prefix (withPosition $ flip (Un op) <$ reservedOp name)

typeAssertion :: Operator StreamType StateType UnderlyingMonad Expression
typeAssertion = Postfix $ withPosition assertion
  where
    assertion = (\lit p e -> TypeAssertion e lit p) <$> (reservedOp ":" >> typeLiteral)

simpleExpression :: Parser Expression
simpleExpression = (ref <|> parens expression <|> funcCall <|> exprLit <|> variable) >>= contOrNo <?> "simple expression"
  where
    ref = withPosition $ reserved "ref" >> Un AddressOf <$> parens expression
    contOrNo prev = cont prev <|> return prev
    cont prev = choice $ map ($ prev) [memberAccess, subscript]

variable :: Parser Expression
variable = withPosition $ Variable <$> identifier

memberAccess :: Expression -> Parser Expression
memberAccess expr = withPosition $ dot >> MemberAccess expr <$> identifier

subscript :: Expression -> Parser Expression
subscript expr = withPosition $ Subscript expr <$> (brackets . many) (brExpr <|> brOp)
  where
    brExpr = Right <$> expression
    brOp = Left <$> operator

funcCall :: Parser Expression
funcCall = withPosition $ try (FuncCall <$> identifier <* openParen) <*> commaSep expression <* closeParen

exprLit :: Parser Expression
exprLit = ExprLit <$> withPosition variants
  where variants = replace reserved "true" (BLit True)
               <|> replace reserved "false" (BLit False)
               <|> replace reserved "null" Null
               <|> replace reserved "_" Undef
               <|> numLit

numLit :: Parser (SourceRange -> Literal)
numLit = either ILit FLit <$> naturalOrFloat

typeDef :: Parser TypeDef
typeDef = withPosition $ newType <|> alias
  where
    tParams = option [] . angles $ commaSep1 identifier
    alias = Alias <$> tParams <*> typeLiteral
    newType = NewType <$> tParams
              <*> option [] (reserved "hide" >> commaSep1 identifier)
              <*> many ((,) <$> identifier <*> replacement)
              <*> many ((,) <$> brPattern <*> replacement)
              <*> typeLiteral
    brPattern = brackets . many $
      (BrId <$> identifier <*> optionMaybe (reservedOp "=" >> expression))
      <|> (BrOp <$> operator)
    replacement = (,) <$> optionMaybe (reservedOp "|" >> expression) <*> expression

typeLiteral :: Parser Type
typeLiteral = simpleTypeLiteral
          <|> namedTypeLiteral
          <|> pointerTypeLiteral
          <|> structTypeLiteral

simpleTypeLiteral :: Parser Type
simpleTypeLiteral = uintTypeLiteral <|> withPosition remainingParser
  where
    remainingParser = choice $ map (uncurry $ replace reserved) typePairs
    typePairs = [ ("I8", IntT S8)
                , ("I16", IntT S16)
                , ("I32", IntT S32)
                , ("I64", IntT S64)
                , ("F32", FloatT S32)
                , ("F64", FloatT S64)
                , ("Bool", BoolT)
                ]

uintTypeLiteral :: Parser Type
uintTypeLiteral = withPosition . choice . map (uncurry $ replace reserved) $ typePairs
  where
    typePairs = [ ("U8", UIntT S8)
                , ("U16", UIntT S16)
                , ("U32", UIntT S32)
                , ("U64", UIntT S64)
                ]

namedTypeLiteral :: Parser Type
namedTypeLiteral = withPosition $ typeVar <|> (NamedT <$> identifier <*> tParams)
  where
    tParams = option [] . angles $ commaSep1 typeLiteral
    typeVar = do
      n@(c:_) <- identifier
      if isLower c then return $ TypeVar n else fail ""

pointerTypeLiteral :: Parser Type
pointerTypeLiteral = withPosition $ reservedOp "$" >> PointerT <$> typeLiteral

structTypeLiteral :: Parser Type
structTypeLiteral = withPosition . braces $ StructT <$> property `sepEndBy` comma
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

openParen :: Parser ()
openParen = void . T.lexeme lexer $ char '('
closeParen :: Parser ()
closeParen = void . T.lexeme lexer $ char ')'

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

data SourceFile = SourceFile
  { typeDefinitions :: [TypeDef]
  , callableDefinitions :: [CallableDef]
  }

data TypeDef = NewType
               { typeParams :: [String]
               , hiddenIdentifiers :: [String]
               , introducedIdentifiers :: [(String, (Maybe Expression, Expression))]
               , bracketPatterns :: [([BracketToken], (Maybe Expression, Expression))]
               , wrappedType :: Type
               , typeRange :: SourceRange
               }
             | Alias
               { typeParams :: [String]
               , wrappedType :: Type
               , typeRange :: SourceRange
               }
data BracketToken = BrId String (Maybe Expression)
                  | BrOp String

data CallableDef = FuncDef
                   { restrictions :: [(String, Restriction)]
                   , intypes :: [Type]
                   , outtype :: Type
                   , inargs :: [String]
                   , outArg :: String
                   , callableBody :: Statement
                   , callableRange :: SourceRange
                   }
                 | ProcDef
                   { restrictions :: [(String, Restriction)]
                   , intypes :: [Type]
                   , outtypes :: [Type]
                   , inargs :: [String]
                   , outargs :: [String]
                   , callableBody :: Statement
                   , callableRange :: SourceRange
                   }

data Type = IntT TSize SourceRange
          | UIntT TSize SourceRange
          | FloatT TSize SourceRange
          | BoolT SourceRange
          | NamedT String [Type] SourceRange
          | TypeVar String SourceRange
          | PointerT Type SourceRange
          | StructT [(String, Type)] SourceRange

data Restriction = PropertiesR [(String, Type)] [([Either String Type], Type)]
                 | UIntR
                 | NumR NumSpec
data NumSpec = NoSpec | IntSpec | FloatSpec

data Statement = ProcCall String [Expression] [Expression] SourceRange
               | Defer Statement SourceRange
               | ShallowCopy Expression Expression SourceRange
               | If Expression Statement (Maybe Statement) SourceRange
               | While Expression Statement SourceRange
               | Scope [Statement] SourceRange
               | Terminator TerminatorType SourceRange
               | VarInit Bool String (Maybe Type) (Maybe Expression) SourceRange

data Expression = Bin BinOp Expression Expression SourceRange
                | Un UnOp Expression SourceRange
                | MemberAccess Expression String SourceRange
                | Subscript Expression [Either String Expression] SourceRange
                | Variable String SourceRange
                | FuncCall String [Expression] SourceRange
                | ExprLit Literal
                | TypeAssertion Expression Type SourceRange

data Literal = ILit Integer SourceRange
             | FLit Double SourceRange
             | BLit Bool SourceRange
             | Null SourceRange
             | Undef SourceRange

class Source a where
  location :: a -> SourceRange
instance Source TypeDef where
  location = typeRange
instance Source CallableDef where
  location = callableRange
instance Source Type where
  location (IntT _ r) = r
  location (UIntT _ r) = r
  location (FloatT _ r) = r
  location (BoolT r) = r
  location (NamedT _ _ r) = r
  location (PointerT _ r) = r
  location (StructT _ r) = r
instance Source Statement where
  location (ProcCall _ _ _ r) = r
  location (Defer _ r) = r
  location (ShallowCopy _ _ r) = r
  location (If _ _ _ r) = r
  location (While _ _ r) = r
  location (Scope _ r) = r
  location (Terminator _ r) = r
  location (VarInit _ _ _ _ r) = r
instance Source Expression where
  location (Bin _ _ _ r) = r
  location (Un _ _ r) = r
  location (MemberAccess _ _ r) = r
  location (Subscript _ _ r) = r
  location (Variable _ r) = r
  location (FuncCall _ _ r) = r
  location (ExprLit l) = location l
  location (TypeAssertion _ _ r) = r
instance Source Literal where
  location (ILit _ r) = r
  location (FLit _ r) = r
  location (BLit _ r) = r
  location (Null r) = r
  location (Undef r) = r
