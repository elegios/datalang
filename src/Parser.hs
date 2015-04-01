{-# LANGUAGE FlexibleContexts, TupleSections #-}

module Parser
( parseFile
, SourceFileT(..)
, TypeDefT(..)
, HiddenIdentifiers(..)
, BracketTokenT(..)
, CallableDefT(..)
, Type(..)
, Restriction(..)
, NumSpec(..)
, StatementT(..)
, ExpressionT(..)
, Literal(..)
) where

import Ast (SourceLoc(..), SourceRange(..), TSize(..), BinOp(..), UnOp(..), TerminatorType(..), Source, location)
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
    makedef c m1 m2 = c <$> identifier
                  <*> restrs
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
procCall = withPosition $ try (ProcCall <$> expression <* char '#') <*> is <*> os
  where
    is = whiteSpace >> commaSep expression
    os = option [] $ reservedOp "#" >> commaSep expression

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
type ExpOp = Operator StreamType StateType UnderlyingMonad Expression
expressionTable :: [[ExpOp]]
expressionTable =
  [ [funcCall, memberAccess, subscript]
  , [pre "-" AriNegate, pre "$" Deref, pre "!" Not]
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
bin :: String -> BinOp -> ExpOp
bin  name op = Infix (withPosition $ (\s e1 e2 -> Bin op e1 e2 s) <$ reservedOp name) AssocLeft

pre :: String -> UnOp -> ExpOp
pre name op = Prefix (withPosition $ flip (Un op) <$ reservedOp name)

postHelp :: (Expression -> i -> SourceRange -> Expression) -> Parser i -> ExpOp
postHelp c p = Postfix . withPosition $ (\i r e -> c e i r) <$> p

funcCall :: ExpOp
funcCall = postHelp FuncCall . parens $ commaSep expression

subscript :: ExpOp
subscript = postHelp Subscript . brackets . many $ brExpr <|> brOp
  where
    brExpr = Right <$> expression
    brOp = Left <$> operator

memberAccess :: ExpOp
memberAccess = postHelp MemberAccess $ dot >> identifier

typeAssertion :: ExpOp
typeAssertion = postHelp TypeAssertion $ reservedOp ":" >> typeLiteral

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

numLit :: Parser (SourceRange -> Literal)
numLit = either ILit FLit <$> naturalOrFloat

typeDef :: Parser TypeDef
typeDef = withPosition $ newType <|> alias
  where
    tParams = option [] . angles $ commaSep1 identifier
    alias = Alias <$> identifier <*> tParams <*> typeLiteral
    newType = NewType <$> identifier <*> tParams
              <*> option (HideSome []) (reserved "hide" >> hidePattern)
              <*> many ((,) <$> identifier <*> replacement)
              <*> many ((,) <$> brPattern <*> replacement)
              <*> typeLiteral
    hidePattern = replace reservedOp "*" HideAll <|> HideSome <$> commaSep1 identifier
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

type SourceFile = SourceFileT String
data SourceFileT v = SourceFile
  { typeDefinitions :: [TypeDefT v]
  , callableDefinitions :: [CallableDefT v]
  }

data HiddenIdentifiers = HideAll | HideSome [String]
type Replacement v = (Maybe (ExpressionT v), ExpressionT v)
type TypeDef = TypeDefT String
data TypeDefT v = NewType
                  { typeName :: String
                  , typeParams :: [String]
                  , hiddenIdentifiers :: HiddenIdentifiers
                  , introducedIdentifiers :: [(String, Replacement v)]
                  , bracketPatterns :: [([BracketTokenT v], Replacement v)]
                  , wrappedType :: Type
                  , typeRange :: SourceRange
                  }
                | Alias
                  { typeName :: String
                  , typeParams :: [String]
                  , wrappedType :: Type
                  , typeRange :: SourceRange
                  }
data BracketTokenT v = BrId String (Maybe (ExpressionT v))
                     | BrOp String

type CallableDef = CallableDefT String
data CallableDefT v = FuncDef
                      { callableName :: String
                      , restrictions :: [(String, Restriction)]
                      , intypes :: [Type]
                      , outtype :: Type
                      , inargs :: [String]
                      , outArg :: String
                      , callableBody :: StatementT v
                      , callableRange :: SourceRange
                      }
                    | ProcDef
                      { callableName :: String
                      , restrictions :: [(String, Restriction)]
                      , intypes :: [Type]
                      , outtypes :: [Type]
                      , inargs :: [String]
                      , outargs :: [String]
                      , callableBody :: StatementT v
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

type Statement = StatementT String
data StatementT v = ProcCall (ExpressionT v) [ExpressionT v] [ExpressionT v] SourceRange
                  | Defer (StatementT v) SourceRange
                  | ShallowCopy (ExpressionT v) (ExpressionT v) SourceRange
                  | If (ExpressionT v) (StatementT v) (Maybe (StatementT v)) SourceRange
                  | While (ExpressionT v) (StatementT v) SourceRange
                  | Scope [StatementT v] SourceRange
                  | Terminator TerminatorType SourceRange
                  | VarInit Bool v (Maybe Type) (Maybe (ExpressionT v)) SourceRange

type Expression = ExpressionT String
data ExpressionT v = Bin BinOp (ExpressionT v) (ExpressionT v) SourceRange
                   | Un UnOp (ExpressionT v) SourceRange
                   | MemberAccess (ExpressionT v) String SourceRange
                   | Subscript (ExpressionT v) [Either String (ExpressionT v)] SourceRange
                   | Variable v SourceRange
                   | FuncCall (ExpressionT v) [ExpressionT v] SourceRange
                   | ExprLit Literal
                   | TypeAssertion (ExpressionT v) Type SourceRange

data Literal = ILit Integer SourceRange
             | FLit Double SourceRange
             | BLit Bool SourceRange
             | Null SourceRange
             | Undef SourceRange

instance Source (TypeDefT v) where
  location = typeRange
instance Source (CallableDefT v) where
  location = callableRange
instance Source Type where
  location (IntT _ r) = r
  location (UIntT _ r) = r
  location (FloatT _ r) = r
  location (BoolT r) = r
  location (NamedT _ _ r) = r
  location (PointerT _ r) = r
  location (StructT _ r) = r
instance Source (StatementT v) where
  location (ProcCall _ _ _ r) = r
  location (Defer _ r) = r
  location (ShallowCopy _ _ r) = r
  location (If _ _ _ r) = r
  location (While _ _ r) = r
  location (Scope _ r) = r
  location (Terminator _ r) = r
  location (VarInit _ _ _ _ r) = r
instance Source (ExpressionT v) where
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
