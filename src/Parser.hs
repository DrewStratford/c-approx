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
    , opLetter = oneOf "-+*/<=>:&|;()~"
    , reservedOpNames = []
    , reservedNames = ["if", "then", "else"
                      , "bool", "int", "float", "list", "True"
                      , "False", "return", "while", "struct"
                      ]
    , caseSensitive = True
    }


parser = makeTokenParser definition

--------------------------------------------------------------------------------
-- parse defintions

parseFuncDef :: Parser String (Definition Var)
parseFuncDef = annotate $ do
  typ   <- parseType
  ident <- identifier parser
  argTypes <- parens parser $ commaSep parser argType
  stmts <- braces parser $ many parseStmt
  return $ ProcDef ident argTypes typ stmts


argType :: Parser String (Var, Type)
argType = do
  typ <- parseType
  ident <- identifier parser
  return (ident, typ)


parseStructDef :: Parser String (Definition Var)
parseStructDef = annotate $ do
  reserved parser "struct"
  ident <- identifier parser
  argTypes <- braces parser $ commaSep parser argType
  return $ StructDef ident (sortStruct argTypes)


parseDefinition :: Parser String (Definition Var)
parseDefinition =  try parseStructDef
               <|> parseFuncDef
               <?> "definition"

--------------------------------------------------------------------------------
-- parse stmts

  

parseAssignment :: Parser String (Stmt Var)
parseAssignment = annotate' $ \pos -> do
  ident <- try $ do i <- identifier parser
                    reservedOp parser "="
                    return i
  exp   <- exprParser
  reservedOp parser ";"
  return $ VarDef (pos :* VarPlaceHolder ident) ident exp

  
parseVarDef :: Parser String (Stmt Var)
parseVarDef = annotate $ do
  typ   <- parseType
  ident <- identifier parser
  reservedOp parser "="
  exp   <- exprParser
  reservedOp parser ";"
  return $ VarDef typ ident exp

  
parseReturn :: Parser String (Stmt Var)
parseReturn = annotate $ do
  try $ reserved parser "return"
  e <- exprParser
  reservedOp parser ";"
  return $ Return e

parseWhile :: Parser String (Stmt Var)
parseWhile = annotate $ do
  try $ reserved parser "while"
  e <- parens parser $ exprParser
  stmts <- braces parser $ many parseStmt
  return $ While 0 e stmts

parseIf :: Parser String (Stmt Var)
parseIf = annotate $ do
  try $ reserved parser "if"
  e <- parens parser $ exprParser
  th <- braces parser $ many parseStmt
  (
    (do try $ do reserved parser "else"
                 lookAhead (reserved parser "if")
        elif <- parseIf
        return $ If 0 e th [elif]
    ) <|>
    (do try $ reserved parser "else"
        el <- braces parser $ many parseStmt
        return $ If 0 e th el) <|>
    (return $ If 0 e th [])
    )

parseFieldAssign :: Parser String (Stmt Var)
parseFieldAssign = annotate' $ \pos -> do
  var    <-  identifier parser
  --field  <-  brackets parser $ identifier parser
  offset  <-  parseAccessor
  reservedOp parser "=" 
  e <- exprParser
  reservedOp parser ";"
  return $ Set (pos :* StructPlaceHolder var) var offset e


parseStmt :: Parser String (Stmt Var)
parseStmt =  try parseVarDef
         <|> try parseAssignment
         <|> parseIf
         <|> parseSetRef
         <|> parseReturn
         <|> parseWhile
         <|> parseFieldAssign
         -- <|> parseVarDef
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
parseFuncCall = annotate' $ \pos -> do
  ident <- identifier parser
  as <- parens parser $ commaSep parser exprParser
  return $ ProcCall (pos :* ProcPlaceHolder ident) as ident

parseList :: Parser String (Val Var)
parseList = annotate $ do
  vs <- braces parser $ commaSep parser parseVal
  return $ A vs

  {-
parseString :: Parser String (Val Var)
parseString = do
  let toI c = I (fromEnum c)
  vs <- map toI <$> (stringLiteral parser)
  return $ A vs
-}

parseAccessor :: Parser String (Offset Var)
parseAccessor = do
  let access = brackets parser $ identifier parser
      toOffset [] =
        error "Parser error: this shouldn't happen because we should parse at least one field"
      toOffset [a] = Off a
      toOffset (a:as) = NestedOff a (toOffset as)
  toOffset <$> many1 access
  

parseStruct :: Parser String (Val Var)
parseStruct = annotate $ do
  let go = do
        typ <- identifier parser
        reservedOp parser ":"
        v   <- exprParser
        return (typ,v)
  vs <- braces parser $ commaSep parser go
  return $ S (sortStruct vs)

parseFieldAccess :: Parser String (Exp Var)
parseFieldAccess = annotate' $ \pos -> do
  var    <-  identifier parser
  --field  <-  brackets parser $ identifier parser
  offset  <-  parseAccessor
  return $ Access (pos :* StructPlaceHolder var) var offset

parseVal :: Parser String (Val Var)
parseVal = try (annotate $ reserved parser "True" >> return (B True))
           <|> try (annotate $ reserved parser "False" >> return (B False))
           <|> try (annotate $ float parser >>= return . F . realToFrac )
           <|> try (annotate $ integer parser >>= return . I . fromInteger)
           <|> parseStruct
           <?> "couldn't parse a value"
  

-- TODO: parse array len
parseType :: Parser String Type
parseType =  (annotate $ reserved parser "bool" >> return Bool)
         <|> (annotate $ reserved parser "int" >> return Int)
         <|> (annotate $ reserved parser "float" >> return Float)
         <|> annotate (
             do reserved parser "ref"
                t <- angles parser parseType
                return $ Ref t
             )
         <|> annotate (
             do reserved parser "struct"
                ident <- identifier parser
                return $ StructPlaceHolder ident
             )
                
         <?> "cant parse a type"


parseSetRef :: Parser String (Stmt Var)
parseSetRef = annotate' $ \pos -> do
  try $ do reservedOp parser "@"
  ident <- identifier parser
  reservedOp parser "="
  e <- exprParser
  reservedOp parser ";"
  return $ Set (pos :* VarPlaceHolder ident) ident (Off "#NO_OFFSET") e

parseGetRef :: Parser String (Exp Var)
parseGetRef = annotate' $ \pos -> do
  try $ reservedOp parser "@"
  ident <- identifier parser
  return $ GetRef (pos :* VarPlaceHolder ident) ident

parseMkRef :: Parser String (Exp Var)
parseMkRef = annotate' $ \pos -> do
  try $ reservedOp parser "&"
  ident <- identifier parser
  return $ MkRef (pos :* VarPlaceHolder ident) ident

parseVar :: Parser String (Exp Var)
parseVar = annotate' $ \pos -> do
  ident <- identifier parser
  return $ Var (pos :* VarPlaceHolder ident) ident


parseTerm :: Parser String (Exp Var)
parseTerm =  try (annotate $ Const <$> parseVal >>= return)
         <|> try (parens parser exprParser)
         <|> try (parseFuncCall)
         <|> try parseFieldAccess
         <|> parseGetRef
         <|> parseMkRef
         <|> parseVar
         <?> "expression"


  

exprTable = [ [ binExp "/" Div]
            , [ binExp "%" Mod]
            , [ binExp "*" Times ]
            , [ binExp "+" Plus ]
            , [ binExp "-" Minus ]
            , [ binExp "/~" FDiv]
            , [ binExp "*~" FTimes ]
            , [ binExp "+~" FPlus ]
            , [ binExp "-~" FMinus ]
            , [ binExp "<" Lt ]
            , [ binExp ">" Gt ]
            , [ binExp "==" Eq ]
            , [ binExp "&&" And ]
            , [ binExp "||" Or ]
            ]

exprParser :: Parser String (Exp Var)
exprParser = buildExpressionParser exprTable parseTerm
             <?> "expression"

------------------------------------------------------------
parseStr :: Parser String a -> String -> Either ParseError a 
parseStr p s = runIdentity $ runParserT p () "" s

parseProg :: String -> Either String (Prog Var)
parseProg = undefined


sortStruct :: Ord a => [(a, b)] -> [(a,b)]
sortStruct = L.sortBy (comparing fst)

sourcePos :: Monad m => ParsecT s u m SourcePos
sourcePos = statePos `liftM` getParserState

annotate :: Parser s (f (Annotated f)) -> Parser s (Annotated f)
annotate a = do
  pos <- sourcePos
  a'  <- a
  return (pos :* a')

-- same as above but passes the source pos to parser
annotate' :: (SourcePos -> Parser s (f (Annotated f))) -> Parser s (Annotated f)
annotate' a = do
  pos <- sourcePos
  a'  <- a pos
  return (pos :* a')
