{-# LANGUAGE UndecidableInstances, PatternSynonyms, ViewPatterns, DeriveFunctor#-}
module AST where

import Control.Monad
import Data.Either
import Data.Ord
import Control.Monad.State as S
import qualified Data.List as L
import System.IO

import Text.Parsec.Pos
import Debug.Trace


data Annotation = Annotation
  { line :: Int
  , col  :: Int
  , src  :: String
  } deriving Show

data Annotated f = SourcePos :*  f (Annotated f) 

instance Show (f (Annotated f)) => Show (Annotated f) where
  show (_ :* f) = show f
instance Eq (f (Annotated f)) => Eq (Annotated f) where
  (_ :* a) == (_ :* b) = a == b

type Prog var = [Definition var]


type Definition a = Annotated (Definition' a)
data Definition' var stmt = ProcDef String [(var,Type)] Type [Stmt var]
                | StructDef String [(Var,Type)] 
                deriving (Show, Eq, Functor)

type Stmt a = Annotated (Stmt' a)
data Stmt' var stmt = VarDef Type var (Exp var)
          | If Int (Exp var) [stmt] [stmt]
          | While Int (Exp var) [stmt]
          | Return (Exp var)
          | VoidReturn 
            deriving (Show, Eq, Functor)

type Exp a = Annotated (Exp' a)
data Exp' var exp = Const (Val var)
         | Var Type  var 
         | Access Type  var var -- Type var, offset(s) 
         | Bin Op exp exp 
         | IfE Int exp exp exp  -- used to expand "Or" statements etc
         | ProcCall Type [exp] String
           deriving (Show, Eq, Functor)

type Val a = Annotated (Val' a)
data Val' var fix = I Int 
      | B Bool 
      | A [fix] 
      | S [(Var, Exp var)]
      deriving (Show, Eq, Functor)

data Op = Plus | Minus | Times | Div | Mod | And | Or | Lt | Gt | Eq | Index | Append
          deriving (Show, Eq, Read)

{-
A procedure is recursive so it can have a return type. This means that procedures that return
procedures are possible although these are not that useful at this stage.
-}

data Type = Bool 
          | Int 
          | Array Int Type 
          | Struct [(Var,Type)]
          | Proc [(Var,Type)] Type 
          | TVar String
          -- A TVar after substitution, signals that it should not be changed
          | TConst String 
          -- These are used as temporary types when parsing and are expanded before checking
          | VarPlaceHolder Var
          | StructPlaceHolder Var
          | ProcPlaceHolder Var
          -- A special type used to store info about a converted procedure that returns a struc
          | SpecReturn Int
          deriving(Show,Eq)

{-
The store is a list of variable names and their values. 
-}


type Var = String

----------------------------------------------------------------------
  -- RENAMING
  -- :this renames each variable to its corresponding offset in the stack
----------------------------------------------------------------------
data StackInfo = SI
  { names :: [(String,Int)]
  , sp :: Int
  }

makeNewStack :: [(Var, Type)] -> RenameM ()
makeNewStack args = do
  let ns = zip vs $ sizedArgs
      (vs, ts) = unzip args
      sp = -4
      sizedArgs = drop 1 $ scanl go 4 ts
      go o x = (o + sizeOf x)
  put (SI ns sp)


toLocal x = "[ebp-" ++ show x ++ "]"

type RenameM a = S.State StackInfo a


renameProg :: Prog Var -> Prog Int
renameProg p = fst $ runState go st 
  where st = SI [] (-4)
        go = mapM renameDef p

renameExp :: Exp Var -> RenameM (Exp Int) 
renameExp (co -> (exp, ann)) = ann <$> case exp of
       Access t@(Struct ss) v off  ->  do
         v' <- changeVar t v
         let off' = lookupStructField ss off
         -- here we also retype the struct to reflect
         -- the return type of the access
         case lookup off ss of
           Just t' -> return (Access t' v' off')
           Nothing -> error "struct access with improper fields"

       Access t v off -> error "struct access with bad type"

       Var t v -> do
         v' <- changeVar t v
         return (Var t v')

       ProcCall t exps n  ->  do
         exps' <- mapM renameExp exps
         return (ProcCall t exps' n)

       Bin o a b  ->  do
         a' <- renameExp a
         b' <- renameExp b
         return (Bin o a' b')

       IfE l cond th el  ->  do
         cond' <- renameExp cond
         th' <- renameExp th
         el' <- renameExp el
         return (IfE l cond' th' el')

       Const val  ->
         renameVal val >>= return . Const


renameVal :: Val Var -> RenameM (Val Int)
renameVal (co -> (val, ann)) = ann <$> case val of
    B b -> return (B b)
    I b -> return (I b)
    A vs -> do
      vs' <- mapM renameVal vs
      return (A vs')
    S vs -> do
      let (ns, es) = unzip vs
      es' <- mapM renameExp es
      return (S $ zip ns es')


renameDef :: Definition String -> RenameM (Definition Int)
renameDef (co -> (def, ann)) = ann <$> case def of
       ProcDef n args typ stmts -> do
         let (argNames, argTypes) = unzip args
         old <- get
         --makeNewStack argNames
         makeNewStack args
         argNames' <- map snd <$> names <$> get
         let args' = zip argNames' argTypes

         stmts' <- mapM rename stmts
         put old
         return (ProcDef n args' typ stmts')
       StructDef n as -> return (StructDef n as)
  

rename :: Stmt String -> RenameM (Stmt Int)
rename (co -> (stmt,ann)) = ann <$> case stmt of
  Return exp -> renameExp exp >>= (return . Return)
  If l exp stmts stmts2 -> do
    exp' <- renameExp exp
    stmts' <- mapM rename stmts
    stmts2' <- mapM rename stmts2
    return (If l exp' stmts' stmts2')
  While l exp stmts -> do
    exp' <- renameExp exp
    stmts' <- mapM  rename stmts
    return (While l exp' stmts')
  VarDef t v exp -> do
    v'   <- changeVar t v
    exp' <- renameExp exp
    return (VarDef t v' exp')
  VoidReturn -> return VoidReturn


getSp :: RenameM Int
getSp = sp <$> get


incSp :: Int -> RenameM ()
incSp size = do
  i <- get
  put i{ sp = sp i - size}


setName :: (Var,Int) -> RenameM ()
setName v = do
  i <- get
  put i{ names = v : names i}

  
changeVar :: Type -> Var -> RenameM Int
changeVar typ v = do
  info <- get
  let n = lookup v (names info)
  case n of
    Just n' -> return n'
    Nothing -> do
      sp <- getSp
      setName (v, sp)
      incSp (sizeOf typ)
      return sp


lookupStructField :: [(Var,Type)] -> Var -> Int
lookupStructField typs var = sum $ map (sizeOf . snd) a
  where (a, _) = break go typs
        go (x,_) = x == var
  

----------------------------------------------------------------------
  -- set the numbering for IF and WHILE stmts. Useful for generating labels.

type LabelM a = S.State Int a

setLabelExp :: Exp a -> LabelM (Exp a)
setLabelExp (co -> (exp,ann)) = ann <$> case exp of
    Bin op l r -> do
      l'  <-  setLabelExp l
      r'  <-  setLabelExp r
      return (Bin op l' r')
    IfE _ c th el -> do
      l    <-  getNextLabel
      c'   <-  setLabelExp c
      th'  <-  setLabelExp th
      el'  <-  setLabelExp el
      return (IfE l c' th' el')
    ProcCall t args x -> do
      args'  <-  mapM setLabelExp args
      return (ProcCall t args' x)

    nonRecursive -> return nonRecursive

  
setLabel :: Stmt v -> LabelM (Stmt v)
setLabel (co -> (stmt,ann)) = ann <$> case stmt of
       If _ exp stmts stmts2  -> do
         l <- getNextLabel
         exp' <- setLabelExp exp
         stmts' <- mapM setLabel stmts
         stmts2' <- mapM setLabel stmts2
         return (If l exp' stmts' stmts2')
       While _ exp stmts  -> do
         l <- getNextLabel
         exp' <- setLabelExp exp
         stmts' <- mapM setLabel stmts
         return (While l exp' stmts')
       VarDef t v exp -> do
         exp' <- setLabelExp exp
         return (VarDef t v exp')
       Return exp -> do
         exp' <- setLabelExp exp
         return (Return exp')
       VoidReturn  -> return VoidReturn

setLabelDef :: Definition v -> LabelM (Definition v)
setLabelDef (co -> (stmt, ann)) = ann <$> case stmt of
       ProcDef n args typ stmts -> do
         let (argNames, argTypes) = unzip args
         stmts' <- mapM setLabel stmts
         return (ProcDef n args typ stmts')
       _ -> return stmt

 
getNextLabel :: LabelM Int
getNextLabel = do
  i <- get
  put (i+1)
  return i

labelProg :: Prog v -> Prog v
labelProg p = fst $ runState go st 
  where st = 1
        go = mapM setLabelDef p


---------------------------------------------------------------------------
  -- Utils


getAllVarDefs :: Stmt v -> [(Type, v)]
getAllVarDefs (_ :* stmt) = case stmt of
  VarDef t v _ -> [(t,v)]
  If _ _ th el -> concatMap getAllVarDefs th ++ concatMap getAllVarDefs el
  While _ _ th -> concatMap getAllVarDefs th
  _                   -> []
          
--TODO check against bad type matches
sizeLocalVars :: Ord v => Definition v -> Int
sizeLocalVars (_ :* ProcDef _ _ _ stmts) = sum (map sizeOf vars)
  where asgns = concatMap getAllVarDefs stmts
        vars  = map (fst . head) $ L.group (L.sortBy (comparing snd) asgns)

sizeArgList :: [(Var,Type)] -> Int
sizeArgList args = sum (map (sizeOf . snd) args)


sizeOf :: Type -> Int
sizeOf typ = case typ of
    Bool -> 4
    Int  -> 4
    Array l t -> l * sizeOf t
    Struct vs -> sum $ map (sizeOf . snd) vs
    Proc _ _ -> 4
    _ -> error $ "err: sizeOf type " ++ show typ

makeGlobalContext :: [Definition Var] -> [(Var,Type)]
makeGlobalContext = map go
  where go (_ :* ProcDef i a t _) = (i, Proc a t )
        go (_ :* StructDef i a) = (i, Struct a)


getAllFuncDefs = filter isFunc
  where isFunc ProcDef{} = True
        isFunc _ = False

{-
  this converts a function returning a struct into a form appropriate for compilation.
  i.e. the return address is the last arg in the function.
-}

convertStructReturning :: Definition Var -> Definition Var
convertStructReturning (co -> (def, ann))= ann $ case def of

  ProcDef n args ty@Struct{} stmts -> (ProcDef n args' (SpecReturn size) stmts')
    where args' = args ++ [("#ret", ty)]
          size = sizeOf ty
          stmts' = concatMap (changeReturns ty) stmts

  _ -> def


handleStructs :: [Definition Var] -> [Definition Var]
handleStructs = map convertStructReturning

changeReturns :: Type -> Stmt Var -> [Stmt Var]
changeReturns t (co -> (stmt, ann)) =
  let recur = concatMap (changeReturns t)
  in ann <$> case stmt of
    Return exp      ->  [VarDef t "#ret" exp, VoidReturn]
    If i exp th el  ->  [If i exp (recur th) (recur el)]
    While i exp th  ->  [While i exp (recur th)]
    s               ->  [s]


--util for returning cofree
returnC a b = return (a :* b)

annotate_ a p = (a :*) p

co  (a :* b) = (b, annotate_ a)
  
flatten (a :* b) = b
flatten2 (a :* b) = flatten <$> b
