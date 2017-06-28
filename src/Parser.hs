{-# LANGUAGE OverloadedStrings #-}
module Parser where

import Control.Monad
import Data.Functor.Identity
import Data.Ord
import qualified Data.List as L

import Text.Parsec
import Text.Parsec.Token
import Text.Parsec.Expr

import AST

type Parser a = Parsec a ()


definition :: LanguageDef st
definition = LanguageDef
    { commentStart = "/*"
    , commentEnd = "*/"
    , commentLine = "//"
    , nestedComments = True
    , identStart = letter
    , identLetter = alphaNum
    , opStart = opLetter definition
    , opLetter = oneOf "-+*/<=>:&|;()"
    , reservedOpNames = []
    , reservedNames = ["if", "then", "else"
                      , "bool", "int", "list", "True"
                      , "False", "return", "while", "struct"
                      ]
    , caseSensitive = True
    }


parser = makeTokenParser definition

--------------------------------------------------------------------------------
-- parse defintions

parseFuncDef :: Parser String (Definition Var)
parseFuncDef = do
  typ   <- parseType
  ident <- identifier parser
  argTypes <- parens parser $ commaSep parser argType
  stmts <- braces parser $ many parseStmt
  annotate $ ProcDef ident argTypes typ stmts


argType :: Parser String (Var, Type)
argType = do
  typ <- parseType
  ident <- identifier parser
  return (ident, typ)


parseStructDef :: Parser String (Definition Var)
parseStructDef = do
  reserved parser "struct"
  ident <- identifier parser
  argTypes <- braces parser $ commaSep parser argType
  annotate $ StructDef ident (sortStruct argTypes)


parseDefinition :: Parser String (Definition Var)
parseDefinition = try parseFuncDef
                  <|> try parseStructDef
                  <?> "expected definition"

--------------------------------------------------------------------------------
-- parse stmts

  

parseAssignment :: Parser String (Stmt Var)
parseAssignment = do
  ident <- identifier parser
  "="   <- operator parser <?> "expected ="
  exp   <- exprParser
  ";"   <- operator parser <?> "expected ;"
  annotate $ VarDef (VarPlaceHolder ident) ident exp

  
parseVarDef :: Parser String (Stmt Var)
parseVarDef = do
  typ   <- parseType
  ident <- identifier parser
  "="   <- operator parser
  exp   <- exprParser
  ";"   <- operator parser <?> "expected ;"
  annotate $ VarDef typ ident exp

  
parseReturn :: Parser String (Stmt Var)
parseReturn = do
  reserved parser "return"
  e <- exprParser
  ";"   <- operator parser <?> "expected ;"
  annotate $ Return e

parseWhile :: Parser String (Stmt Var)
parseWhile = do
  reserved parser "while"
  e <- parens parser $ exprParser
  stmts <- braces parser $ many parseStmt
  annotate $ While 0 e stmts

parseIf :: Parser String (Stmt Var)
parseIf = do
  reserved parser "if"
  e <- parens parser $ exprParser
  th <- braces parser $ many parseStmt
  reserved parser "else"
  el <- braces parser $ many parseStmt
  annotate $ If 0 e th el


parseStmt :: Parser String (Stmt Var)
parseStmt = try parseAssignment
         <|> try parseVarDef
         <|> try parseIf
         <|> try parseReturn
         <|> try parseWhile
         <?> "failed to parse Stmt"
         

program :: Parser String (Prog Var)
program = do
  defs <- many parseDefinition
  eof
  return defs
------------------------------------------
  -- parse expressions

binExp :: String -> Op -> Operator String u Identity (Exp Var)
binExp p op = 
  let t = do
        s <- sourcePos 
        reservedOp parser p
        return $ \a b -> (s :* Bin op a b)
  in (Infix t AssocLeft)

    
parseFuncCall :: Parser String (Exp Var)
parseFuncCall = do
  ident <- identifier parser
  as <- parens parser $ commaSep parser exprParser
  annotate $ ProcCall (ProcPlaceHolder ident) as ident

parseList :: Parser String (Val Var)
parseList = do
  vs <- braces parser $ commaSep parser parseVal
  annotate $ A vs

  {-
parseString :: Parser String (Val Var)
parseString = do
  let toI c = I (fromEnum c)
  vs <- map toI <$> (stringLiteral parser)
  annotate $ A vs
-}

parseStruct :: Parser String (Val Var)
parseStruct = do
  let go = do
        typ <- identifier parser
        ":"   <- operator parser <?> "expected :"
        v   <- exprParser
        return (typ,v)
  vs <- braces parser $ commaSep parser go
  annotate $ S (sortStruct vs)

parseFieldAccess :: Parser String (Exp Var)
parseFieldAccess = do
  var    <-  identifier parser
  field  <-  brackets parser $ identifier parser
  annotate $ Access (StructPlaceHolder var) var field

parseVal :: Parser String (Val Var)
parseVal = try (reserved parser "True" >> annotate (B True))
           <|> try (reserved parser "False" >> annotate (B False))
           <|> try (integer parser >>= annotate . I . fromInteger)
           <|> try parseStruct
           <?> "couldn't parse a value"
  

-- TODO: parse array len
parseType :: Parser String Type
parseType =  (reserved parser "bool" >> return Bool)
         <|> (reserved parser "int" >> return Int)
         <|> do reserved parser "array"
                t <- angles parser parseType
                return $ Array 10 t
         <|> do reserved parser "struct"
                ident <- identifier parser
                return $ StructPlaceHolder ident
                
         <?> "cant parse a type"


parseTerm :: Parser String (Exp Var)
parseTerm = try (Const <$> parseVal >>= annotate)
         <|> try (parens parser exprParser)
         <|> try (parseFuncCall)
         <|> try parseFieldAccess
         <|> try (do
                    ident <- identifier parser
                    annotate $ Var (VarPlaceHolder ident) ident
                 )
         <?> "expected expression"


  

exprTable = [ [ binExp "/" Div]
            , [ binExp "%" Div]
            , [ binExp "*" Times ]
            , [ binExp "+" Plus ]
            , [ binExp "-" Minus ]
            , [ binExp "<" Lt ]
            , [ binExp ">" Gt ]
            , [ binExp "==" Eq ]
            , [ binExp "&&" And ]
            , [ binExp "||" Or ]
            , [ binExp "!!" Index ]
            , [ binExp "++" Append ]
            ]

exprParser :: Parser String (Exp Var)
exprParser = buildExpressionParser exprTable parseTerm
             <?> "expected expression"

------------------------------------------------------------
parseStr :: Parser String a -> String -> Either ParseError a 
parseStr p s = runIdentity $ runParserT p () "" s

parseProg :: String -> Either String (Prog Var)
parseProg = undefined


sortStruct :: Ord a => [(a, b)] -> [(a,b)]
sortStruct = L.sortBy (comparing fst)

sourcePos :: Monad m => ParsecT s u m SourcePos
sourcePos = statePos `liftM` getParserState

annotate :: f (Annotated f) -> Parser s (Annotated f)
annotate a = do
  pos <- sourcePos
  return (undefined :* a)
