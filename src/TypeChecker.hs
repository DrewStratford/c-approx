{-# LANGUAGE ViewPatterns #-}
module TypeChecker where

import AST
import Control.Monad
import Control.Monad.State as S
import qualified Data.List as L

import Debug.Trace

import Text.Parsec.Pos

type Context = [(Var, Type)]


safeLast [] = Nothing
safeLast a  = Just (last a)


type ContextM a = S.StateT Context (Either String) a

getTypeVal :: Val String -> ContextM Type
getTypeVal (co -> (val,ann)) = ann <$> case val of
       B b -> return Bool
       I b -> return Int
       F b -> return Float
       A vs -> error "implement arrays"
       S elems -> do
         let (ns, vs) = unzip elems
         vs' <- mapM getTypeExp vs
         return (Struct $ zip ns vs')

getTypeBinOp :: Op -> Type -> Type -> ContextM Type
getTypeBinOp op l r = case (l, op, r) of
  (ann :* Float, FPlus, _:* Float)  -> return $ ann :* Float
  (ann :* Float, FMinus, _:* Float) -> return $ ann :* Float
  (ann :* Float, FTimes, _:* Float) -> return $ ann :* Float
  (ann :* Float, FDiv, _:* Float)   -> return $ ann :* Float

  (ann :* Int, Plus, _:* Int)  -> return $ ann :* Int
  (ann :* Int, Minus, _:* Int) -> return $ ann :* Int
  (ann :* Int, Times, _:* Int) -> return $ ann :* Int
  (ann :* Int, Div, _:* Int)   -> return $ ann :* Int
  (ann :* Int, Mod, _:* Int)   -> return $ ann :* Int
  (ann :* Int, Lt, _:* Int)    -> return $ ann :* Bool
  (ann :* Int, Gt, _:* Int)    -> return $ ann :* Bool
  (ann :* Int, Eq, _:* Int)    -> return $ ann :* Bool
  (ann :* Bool, Eq, _:* Bool)  -> return $ ann :* Bool
  (ann :* Bool, And, _:* Bool)  -> return $ ann :* Bool
  (ann :* Bool, Or, _:* Bool)  -> return $ ann :* Bool
  (ann :* Ref{}, Eq, _:* Ref{}) -> return $ ann :* Bool
  (ann :* _, _, _ )            -> typeError ann "misapplied operator"

getTypeExp :: (Exp Var) -> ContextM Type
getTypeExp (ann :* exp) = case exp of
       Bin op l r -> do
         l' <- getTypeExp l
         r' <- getTypeExp r
         getTypeBinOp op l' r' 
       IfE _ c th el -> do
         (_ :* cond) <- getTypeExp c
         if cond == Bool
           then do
           th' <- getTypeExp th
           el' <- getTypeExp el
           if th' == el'
             then return th'
             else typeError ann "IfE expressions aren't the same type"

           else typeError ann "condition in If doesn't return bool"
       ProcCall (_ :* Proc argTypes retType) args name -> do
         args' <- mapM getTypeExp args
         if args' == (map snd argTypes)
           then return retType
           else typeError ann $ "badly typed arguments in call:" ++ name
       Access typ@(_ :* Struct fieldTypes) v off -> do
         varTyp <- lookupType ann v
         if varTyp == typ
           then expandError ann "struct doesn't have field " (getFieldType fieldTypes off)
           else typeError ann "variable doesn't match struct type"
       Var typ v            -> return typ
       MkRef typ v          -> return typ
       GetRef (_:* Ref t) v -> return t
       Const val            -> getTypeVal val
       -- casts should only work when types are the same size
       Cast castingTo exp   -> do
         castingFrom <- getTypeExp exp
         typeGuard (sizeOf castingFrom == sizeOf castingTo) ann "casting to a size that doesn't match"
         return castingTo
         

       nonRecursive -> typeError ann "cant type expression"

getTypeStmt :: Type -> Stmt Var -> ContextM ()
getTypeStmt returnType (ann :* stmt) = case stmt of
  Set (_:* Ref t) v _ exp -> do
    exp' <- getTypeExp exp
    if t == exp'
      then return ()
      else typeError ann "setting reference with wrong type"
  Set s@(ann:* Struct fieldTypes) v off exp -> do
    varTyp <- lookupType ann v
    fieldType <- expandError ann "struct doesn't have field " (getFieldType fieldTypes off)
    exp'      <- getTypeExp exp
    if varTyp == s && fieldType == exp'
      then return ()
      else typeError ann "setting variable doesn't match struct type"
  If _ c th el -> do
    (_ :* cond) <- getTypeExp c
    if cond == Bool
      then do
      th' <- mapM (getTypeStmt returnType) th
      el' <- mapM (getTypeStmt returnType) el
      return ()
    else typeError ann "condition in If doesn't return bool"
  While _ c th -> do
    (_ :* cond) <- getTypeExp c
    if cond == Bool
      then do
      th' <- mapM (getTypeStmt returnType) th
      return ()
    else typeError ann "condition in If doesn't return bool"
  VarDef typ var exp -> do
    expType <- getTypeExp exp
    if typ == expType
      then insertType (var, typ)
      else typeError ann $ "exp doesn't match type its being assigned to " ++ show (typ, expType)
  VoidReturn -> return ()
  Return exp  -> do
    exp' <- getTypeExp exp
    if exp' == returnType
      then return ()
      else typeError ann "exp doesn't match return type"
  
getTypeDef :: Definition Var -> ContextM ()
getTypeDef (ann :* def) = case def of
  StructDef{} -> return ()
  ProcDef name args returnType stmts -> do
    oldCntxt <- get
    insertTypes args
    mapM_ (getTypeStmt returnType) stmts
    checkForGuranteedReturn ann stmts
    put oldCntxt

typeCheckProg :: Context -> Prog Var -> Either String ()
typeCheckProg context prog = fst <$> runStateT (mapM_ getTypeDef prog) context
  

{- we need to check that all functions gurantee a return -}

checkForGuranteedReturn :: SourcePos -> [Stmt a] -> ContextM ()
checkForGuranteedReturn ann stmts = if doesReturn
  then return ()
  else typeError ann "function does not gurantee return"
  where doesReturn = any isReturn stmts
{-
Small helper to check return types. We consider an if statment where both branches return to be
suitable.
-}

isReturn :: Stmt a -> Bool
isReturn (_ :* Return _) = True
isReturn (_ :* If _ _ th el) = any isReturn th && any isReturn el
isReturn _          = False
{-
expands the types of statements so that there are no place holder types
-}


expandTypeExp :: (Exp Var) -> ContextM (Exp Var)
expandTypeExp (ann :* exp) = (ann :*) <$> 
  case exp of
       Bin op l r -> do
         l' <- expandTypeExp l
         r' <- expandTypeExp r
         return (Bin op l' r')
       IfE l c th el -> do
         c' <- expandTypeExp c
         th' <- expandTypeExp th
         el' <- expandTypeExp el
         return (IfE l c' th' el')
       ProcCall (_:* ProcPlaceHolder p) args x -> do
         typ   <- lookupType ann p >>= typeExpand
         args' <- mapM expandTypeExp args
         return (ProcCall typ args' x)
       ProcCall t args x -> do
         args' <- mapM expandTypeExp args
         t' <- typeExpand t
         return (ProcCall t' args' x)
       Access (_:* StructPlaceHolder t) v off -> do
         typ' <- lookupType ann t >>= typeExpand
         return (Access typ' v off)
       Access (_:* VarPlaceHolder t) v off -> do
         typ' <- lookupType ann t >>= typeExpand
         return (Access typ' v off)
       Var (_:* VarPlaceHolder t) v -> do
         typ' <- lookupType ann t >>= typeExpand
         return (Var typ' v)
       Var (_:* StructPlaceHolder t) v -> do
         typ' <- lookupType ann t >>= typeExpand
         return (Var typ' v)
       MkRef (_:* VarPlaceHolder t) v -> do
         t'@(ann :* typ') <- lookupType ann t >>= typeExpand
         return (MkRef (ann :* Ref t') v)
       MkRef (_:* StructPlaceHolder t) v -> do
         typ' <- lookupType ann t >>= typeExpand
         return (MkRef typ' v)
       GetRef (_:* VarPlaceHolder t) v -> do
         typ' <- lookupType ann t >>= typeExpand
         return (GetRef typ' v)
       GetRef (_:* StructPlaceHolder t) v -> do
         typ' <- lookupType ann t >>= typeExpand
         return (GetRef typ' v)

       Const val -> Const <$> expandTypeVal val 
       Cast typ exp -> Cast <$> typeExpand typ <*> expandTypeExp exp

       nonRecursive -> return nonRecursive

  
expandType :: (Stmt Var) -> ContextM (Stmt Var)
expandType (ann :* stmt) = (ann :* ) <$> case stmt of
       If l exp stmts stmts2 -> do
         exp' <- expandTypeExp exp
         stmts' <- mapM expandType stmts
         stmts2' <- mapM expandType stmts2
         return (If l exp' stmts' stmts2')
       While l exp stmts -> do
         exp' <- expandTypeExp exp
         stmts' <- mapM expandType stmts
         return (While l exp' stmts')
       VarDef (_:* VarPlaceHolder t) v exp -> do
         typ  <- lookupType ann t >>= typeExpand
         exp' <- expandTypeExp exp
         insertType (v, typ)
         return (VarDef typ v exp')
       VarDef (_:* StructPlaceHolder t) v exp -> do
         typ  <- lookupType ann t >>= typeExpand
         exp' <- expandTypeExp exp
         insertType (v, typ)
         return (VarDef typ v exp')
       VarDef t v exp -> do
         exp' <- expandTypeExp exp
         insertType (v, t)
         return (VarDef t v exp')
       Return exp -> do
         exp' <- expandTypeExp exp
         return (Return exp')
       Set (_:* StructPlaceHolder t) v off exp -> do
         exp' <- expandTypeExp exp
         typ' <- lookupType ann t >>= typeExpand
         return (Set typ' v off exp')
       Set (_:* VarPlaceHolder t) v off exp -> do
         exp' <- expandTypeExp exp
         typ' <- lookupType ann t >>= typeExpand
         return (Set typ' v off exp')


expandTypeDef :: (Definition Var) -> ContextM (Definition Var)
expandTypeDef (ann :* def) = (ann :*) <$> case def of
       ProcDef n args typ stmts -> do
         let (argNames, argTypes) = unzip args
         -- we need to get the old context
         oldContext <- get
         args' <-  zip argNames <$> mapM typeExpand argTypes
         insertTypes args'

         typ' <- typeExpand typ
         stmts' <- mapM expandType stmts

         put oldContext
         return (ProcDef n args' typ' stmts')

       StructDef n vs -> do
         vs' <- mapM typeExpandArg vs
         insertType (n, ann :* Struct vs')
         return (StructDef n vs')


expandTypeProg :: Context -> (Prog Var) -> Either String (Prog Var)
expandTypeProg cntxt prog = 
  fst <$> runStateT (mapM expandTypeDef prog) cntxt
  

expandContext :: Context -> Either String Context
expandContext cntxt = do
  fst <$> runStateT (mapM typeExpandArg cntxt) cntxt

typeExpandArg :: (a,Type) -> ContextM (a,Type)
typeExpandArg (a, t) = do
  t' <- typeExpand t
  return (a, t')
  
typeExpand :: Type -> ContextM Type
typeExpand (pos :* ty) = case ty of
  VarPlaceHolder v    -> lookupType pos v
  ProcPlaceHolder v   -> lookupType pos v
  StructPlaceHolder v -> lookupType pos v
  Ref typ -> do
    typ' <- typeExpand typ
    return (pos :* Ref typ')
  Proc as ret -> do
    as' <- mapM typeExpandArg as
    ret' <- typeExpand ret
    return (pos :* Proc as' ret')
  Struct as -> do
    as' <- mapM typeExpandArg as
    return (pos :* Struct as')
  t -> return (pos :* t)

expandTypeVal :: Val String -> ContextM (Val Var)
expandTypeVal (ann :* val) = (ann :*) <$> case val of
       B b -> return (B b)
       I b -> return (I b)
       F b -> return (F b)
       A vs -> do
         vs' <- mapM expandTypeVal vs
         return (A vs')
       S elems -> do
         let (ns, vs) = unzip elems
         vs' <- mapM expandTypeExp vs
         return (S $ zip ns vs')
  
-- TO CONSIDER: should this return annotated types?
lookupType :: SourcePos -> Var -> ContextM Type
lookupType pos v = do
  context <- get
  let t = L.lookup v context
  case t of
    Nothing -> lift $ Left (show pos ++ ": couldn't find type of: " ++ v)
    Just t' -> return t'
  
insertType :: (Var, Type) -> ContextM ()
insertType typ = do
  context <- get
  put (typ:context)

insertTypes :: Context -> ContextM ()
insertTypes = mapM_ insertType


typeError ann msg = lift $ Left $ show ann ++ ": type error, " ++ msg 

expandError :: SourcePos -> String -> Either String b -> ContextM b
expandError ann msg err = case err of
  Right val -> return val
  Left err' -> lift (Left $ show ann ++ ": type error, " ++ msg ++ err')

{-
 - A version of gaurd that causes a typeError on failure
 -}
typeGuard :: Show ann => Bool -> ann -> String -> ContextM ()
typeGuard b ann msg = case b of
  True -> return ()
  False -> (typeError ann msg)
