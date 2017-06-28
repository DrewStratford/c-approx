
import Control.Monad.State as S
import qualified Data.List as L
import System.Environment
import System.IO
import Text.Parsec

import Debug.Trace

import Parser
import AST
import TypeChecker

  {-
link output using:
    nasm -f elf32 file.asm -F dwarf && gcc -m32 file.o

  NOTE: the runtime assumes it is being linked by gcc
-}
main = do
  args <- getArgs
  let fileName = args !! 0
  content <- readFile fileName
  let ast =  do parseStr program content
  case ast of
    Left err -> print err
    Right ast' -> do
        let cntxt = builtinFuncs ++ makeGlobalContext ast'
            returns prog = handleStructs <$>  (expandTypeProg cntxt prog)
            --renamed = compileAll <$> labelProg <$> renameProg <$> (returns $ getAllFuncDefs ast')
            --renamed = labelProg <$> renameProg <$> (returns $ getAllFuncDefs ast')
            expanded :: Either String (Prog Var)
            expanded = returns $ ast'
            renamed = renameProg <$> expanded
            compiled = compileAll <$> labelProg <$> renamed
            --compiled = labelProg <$> renamed
        case compiled of
          Left err -> print err
          Right compiled' -> do
            putStrLn header
            putStrLn message
            putStrLn printf
            putStrLn get'
            putStrLn set
            putStrLn "\n"
            putStrLn ";; program begin"
            putStrLn "\n"
            mapM_ putStrLn compiled'
            --mapM_ print compiled'


binOpToAsm op =
  let arith x = ["pop ebx", "pop eax", x ++ " eax,ebx", "push eax"]
      logic x = ["pop ebx", "pop eax",
                 "cmp eax,ebx", x ++ " al", "movzx eax, al",
                 "push eax"]
      divis   = ["pop ebx", "xor edx, edx,", "pop eax", "div ebx", "push eax"]
      modulo  = ["pop ebx", "xor edx, edx,", "pop eax", "div ebx", "push edx"]
  in case op of
        Plus  -> arith "add"
        Minus -> arith "sub"
        Times -> arith "imul"
        Div   -> divis
        Mod   -> modulo
        Eq    -> logic "sete"
        Gt    -> logic "setg"
        Lt    -> logic "setl"


loadIToAsm i = ("mov ecx, " ++ i): ["push ecx"]
loadToAsm i = ("mov ecx, " ++ i): ["push ecx"]
storeToAsm i = "pop ecx" : ["mov " ++ showVariable i ++ ", ecx"]
loadToAsmOff i off = ["lea edx, " ++ i
                     , "mov ecx, [edx " ++ offset ++ "]"
                     , "push ecx"]
  where offset = if off == 0 then "" else show (-off)
  --where offset = if off < 0 then show off else "+" ++ show off

structAddresses start size = init [start, start - 4 .. start - size]

loadStructImm vs = concatMap (expToAsm) values
  where (ns, values) = unzip vs

loadStruct :: Int -> Int -> [String]
loadStruct start size = concatMap go (structAddresses start size)
  where go x = [ "mov ecx," ++ showVariable (x)
               , "push ecx"
               ]

-- FIXME: the offset addresses aren't being calculated properly
loadStructOff :: Int -> Int -> Int -> [String]
loadStructOff start size off =
    setUp ++ concatMap go ([0,4 .. size -1])
  where go x = [ "mov ecx," ++ showRef x
               , "push ecx"
               ]
        setUp = ["lea edx, " ++ showVariable (start-off)]
        showRef x = "[edx -" ++ show x ++ "]"

storeStruct :: Int -> Int -> [String]
storeStruct start size = concatMap go (reverse $ structAddresses start size)
  where go x = [ "pop ecx"
               , "mov " ++ showVariable (x) ++ ", ecx"
               ]

showVal v = case v of
  I i -> show i
  B True -> "1"
  B False -> "0"
  _ -> error "cant show lists yet"


expToAsm exp = case exp of
  Const (S vs)  -> loadStructImm vs
  Const v       -> loadIToAsm (showVal v)
  --TODO This doesn't properly load an embedded struct
  Access s@Struct{} v off -> loadStructOff v (sizeOf s) off
  Access _ v off     -> loadToAsmOff (showVariable v) off
  Var s@(Struct _) v -> loadStruct v (sizeOf s)
  Var _ v       -> loadToAsm (showVariable v)
  Bin op e1 e2  -> expToAsm e1 ++ expToAsm e2 ++ binOpToAsm op

  --this is a call that "returns" a struct
  -- we must make special care that the return (i.e. the first arg)
  -- is still on the stack after clean up.
  -- Also, we must make space for the return before the call.
  ProcCall (Proc args (s@Struct{})) exps name ->
      setUp : concatMap expToAsm (reverse exps) ++ ["call " ++ name, cleanUp]
    --where cleanUp = "add esp," ++ show (4 * length exps)
    where cleanUp = "add esp," ++ show (sizeArgList args )
          setUp   = "sub esp," ++ show (sizeOf s)

  ProcCall (Proc args ret) exps name ->
    concatMap expToAsm (reverse exps)++ ["call " ++ name, cleanUp, "push eax"]
    --where cleanUp = "add esp," ++ show (4 * length exps)
    where cleanUp = "add esp," ++ show (sizeArgList args)

  IfE l exp th el -> expToAsm exp ++ cnd  ++ stmtsT ++ stmtsE
    where elL    = ".EXP_IF_EL_" ++ show l
          endL   = ".EXP_IF_END_" ++ show l
          cnd    = compare' ++ ["je " ++ elL]
          stmtsT = expToAsm th ++ ["jmp " ++ endL]
          stmtsE = (elL ++ ":") : expToAsm el ++ [endL ++ ":"]
  
showVariable x = if x < 0
  then "[ebp " ++ show x ++ "]"
  else "[ebp +" ++ show x ++ "]"


stmtToAsm :: Stmt Int -> [String]
stmtToAsm stmt = case stmt of
  VarDef s@(Struct vs) v exp -> expToAsm exp ++ storeStruct v (sizeOf s)
  --VarDef _ v (Const val) -> ["mov ecx, " ++ showVal val, "mov " ++ v ++ ", ecx"]
  VarDef _ v (Const val) -> ["mov ecx, " ++ showVal val
                            , "mov " ++ showVariable v ++ ", ecx"]
  VarDef _ v (Var _ var) -> ["mov ecx, " ++ showVariable var
                            , "mov " ++ showVariable v ++ ", ecx"]
  VarDef _ v exp -> expToAsm exp ++ storeToAsm v

  If l exp th el -> expToAsm exp ++ cnd  ++ stmtsT ++ stmtsE
    where elL = ".IF_EL_" ++ show l
          endL = ".IF_END_" ++ show l
          cnd = compare' ++ ["je " ++ elL]
          stmtsT = concatMap stmtToAsm th ++ ["jmp " ++ endL]
          stmtsE = (elL ++ ":") : concatMap stmtToAsm el ++ [endL ++ ":"]
  While l exp th -> (startL ++ ":"):expToAsm exp ++ cnd ++ stmts ++ ["jmp " ++ startL, endL ++ ":"]
    where endL = ".WH_END_" ++ show l
          startL = ".WH_" ++ show l
          cnd = compare' ++ ["je " ++ endL]
          stmts = concatMap stmtToAsm th
  Return exp   -> expToAsm exp ++ ["pop eax","leave","ret"]
  VoidReturn -> ["leave","ret"]


definitionToAsm def = case def of
  ProcDef label _ _ stmts ->
    [label ++ ":"] ++ makeRoom ++ concatMap stmtToAsm stmts 
    where makeRoom = ["push ebp", "mov ebp, esp", "sub esp, " ++ localVars]
          localVars = show $ sizeLocalVars def 
  --StructDef{} -> ["error attempting to compile a struct"]
  StructDef{} -> []

  
compileAll :: Prog Int -> [String]
compileAll p = concatMap definitionToAsm p

compare' = ["pop eax", "cmp eax,0"]

header =
  "section .text\n global main\n extern printf\nextern malloc\nextern free"

message = "message db \"answer = %d\", 10,0"
entry = "_start:\n call begin\nret\n\n"

printf = concat
  [ "putChr:\n"
  , "push ebp \n"
  , "mov ebp, esp\n"
  , "mov eax, [ebp+8] \n"
  , "push eax \n"
  , "push message \n"
  , "call printf \n"
  , "add esp, 8 \n"
  , "mov eax, [ebp+8] \n"
  , "leave\n"
  , "ret"
  ]

set = concat
  [ "set:\n"
  , "push ebp \n"
  , "mov ebp, esp\n"
  , "mov eax, [ebp+8] \n"
  , "mov ebx, [ebp+12] \n"
  , "mov [eax], ebx \n"
  , "mov eax, 1 \n"
  , "leave\n"
  , "ret"
  ]

get' = concat
  [ "get:\n"
  , "push ebp \n"
  , "mov ebp, esp\n"
  , "mov eax, [ebp+8] \n"
  , "mov eax, [eax] \n"
  , "leave\n"
  , "ret"
  ]

builtinFuncs = [("putChr", Proc [("",Int)] Int)
               ,("set", Proc [("",Int),("",Int)] Int)
               , ("get", Proc [("",Int)] Int)
               ]
