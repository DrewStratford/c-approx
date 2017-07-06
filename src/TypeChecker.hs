module TypeChecker where

import AST
import Control.Monad
import Control.Monad.State as S
import qualified Data.List as L

import Text.Parsec.Pos

type Context = [(Var, Type)]

{-
subType :: String -> Type -> Type -> Type
subType i repl typ =
  let recur  = subType i repl
      recur' = subTypeTup i repl
  in case typ of
    TVar i' | i == i'     -> makeConst repl
    TVar j                -> TVar j
    TConst j              -> TConst j
    Array size t'         -> Array size (recur t')
    Proc types t          -> Proc (map recur' types) (recur t)
    Struct types          -> Struct (map recur' types)
    Int                   -> Int
    Bool                  -> Bool
    -- these should never come up as they should be expanded
    v@VarPlaceHolder{}    -> v
    v@StructPlaceHolder{} -> v
    v@ProcPlaceHolder{}   -> v


subTypeTup :: String -> Type -> (a, Type) -> (a,Type)
subTypeTup i repl (a, typ) = (a, subType i repl typ)


-- Attempts to unify two types and return the result (t2 must be a subset of t1)
unifyType :: Type -> Type -> Maybe Type
unifyType t1 t2 = case (t1, t2) of
  -- a tvar on the right can be anything
  (TVar i, tr)             -> return tr
  -- a Tvar on the right will not match with anything
  (_, TVar _)              -> Nothing
  (Struct as, Struct bs)   -> do
                              a <- unifyList (map snd as) (map snd bs)
                              return $ Struct (zip (map fst as) a)
  (Proc as ra, Proc bs rb) -> do
                              a <- unifyList (map snd as ++ [ra]) (map snd bs ++ [rb])
                              ret <- safeLast a
                              let args = zip (map fst bs) (init a)
                              return (Proc args ret)

  _ | t1 == t2             -> return t1
  _                        -> Nothing



unifyList :: [Type] -> [Type] -> Maybe [Type]
unifyList [] [] = return []
unifyList []  _ = Nothing
unifyList ts [] = return ts
unifyList (a:as) (b:bs) =
  let remaining = unifyList as bs
      subbed s t = return (b:) <*> unifyList (map (subType s t) as) bs
  in case (a,b) of
    (TVar i, t)  -> subbed i t
    (x, y)       -> do
                    t' <- x `unifyType` y
                    (t':) <$> remaining

  
makeConst :: Type -> Type
makeConst (TVar t) = TConst t
makeConst a        = a
-}

safeLast [] = Nothing
safeLast a  = Just (last a)




{-
expands the types of statements so that there are no place holder types
-}

type ContextM a = S.StateT Context (Either String) a

expandTypeExp :: (Exp Var) -> ContextM (Exp Var)
expandTypeExp (ann :* exp) =
  let return' = returnC ann
  in case exp of
       Bin op l r -> do
         l' <- expandTypeExp l
         r' <- expandTypeExp r
         return' (Bin op l' r')
       IfE l c th el -> do
         c' <- expandTypeExp c
         th' <- expandTypeExp th
         el' <- expandTypeExp el
         return' (IfE l c' th' el')
       ProcCall (_:* ProcPlaceHolder p) args x -> do
         typ   <- lookupType ann p >>= typeExpand
         args' <- mapM expandTypeExp args
         return' (ProcCall typ args' x)
       ProcCall t args x -> do
         args' <- mapM expandTypeExp args
         t' <- typeExpand t
         return' (ProcCall t' args' x)
       Access (_:* StructPlaceHolder t) v off -> do
         typ' <- lookupType ann t >>= typeExpand
         return' (Access typ' v off)
       Access (_:* VarPlaceHolder t) v off -> do
         typ' <- lookupType ann t >>= typeExpand
         return' (Access typ' v off)
       Var (_:* VarPlaceHolder t) v -> do
         typ' <- lookupType ann t >>= typeExpand
         return' (Var typ' v)
       Var (_:* StructPlaceHolder t) v -> do
         typ' <- lookupType ann t >>= typeExpand
         return' (Var typ' v)
       MkRef (_:* VarPlaceHolder t) v -> do
         typ' <- lookupType ann t >>= typeExpand
         return' (MkRef typ' v)
       MkRef (_:* StructPlaceHolder t) v -> do
         typ' <- lookupType ann t >>= typeExpand
         return' (MkRef typ' v)
       GetRef (_:* VarPlaceHolder t) v -> do
         typ' <- lookupType ann t >>= typeExpand
         return' (GetRef typ' v)
       GetRef (_:* StructPlaceHolder t) v -> do
         typ' <- lookupType ann t >>= typeExpand
         return' (GetRef typ' v)

       Const val -> expandTypeVal val >>= return' . Const

       nonRecursive -> return' nonRecursive

  
expandType :: (Stmt Var) -> ContextM (Stmt Var)
expandType (ann :* stmt) =
  let return' = returnC ann
  in case stmt of
       If l exp stmts stmts2 -> do
         exp' <- expandTypeExp exp
         stmts' <- mapM expandType stmts
         stmts2' <- mapM expandType stmts2
         return' (If l exp' stmts' stmts2')
       While l exp stmts -> do
         exp' <- expandTypeExp exp
         stmts' <- mapM expandType stmts
         return' (While l exp' stmts')
       VarDef (_:* VarPlaceHolder t) v exp -> do
         typ  <- lookupType ann t >>= typeExpand
         exp' <- expandTypeExp exp
         insertType (v, typ)
         return' (VarDef typ v exp')
       VarDef (_:* StructPlaceHolder t) v exp -> do
         typ  <- lookupType ann t >>= typeExpand
         exp' <- expandTypeExp exp
         insertType (v, typ)
         return' (VarDef typ v exp')
       VarDef t v exp -> do
         exp' <- expandTypeExp exp
         insertType (v, t)
         return' (VarDef t v exp')
       Return exp -> do
         exp' <- expandTypeExp exp
         return' (Return exp')
       Set (_:* StructPlaceHolder t) v off exp -> do
         exp' <- expandTypeExp exp
         typ' <- lookupType ann t >>= typeExpand
         return' (Set typ' v off exp')
       Set (_:* VarPlaceHolder t) v off exp -> do
         exp' <- expandTypeExp exp
         typ' <- lookupType ann t >>= typeExpand
         return' (Set typ' v off exp')


expandTypeDef :: (Definition Var) -> ContextM (Definition Var)
expandTypeDef (ann :* def) =
  let return' = returnC ann
  in case def of
       ProcDef n args typ stmts -> do
         let (argNames, argTypes) = unzip args
         -- we need to get the old context
         oldContext <- get
         args' <-  zip argNames <$> mapM typeExpand argTypes
         insertTypes args'

         typ' <- typeExpand typ
         stmts' <- mapM expandType stmts

         put oldContext
         return' (ProcDef n args' typ' stmts')

       -- TODO: we need to expand embedded structs
       StructDef n vs -> do
         vs' <- mapM typeExpandArg vs
         insertType (n, ann :* Struct vs')
         return' (StructDef n vs')


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
expandTypeVal (ann :* val) =
  let return' = returnC ann
  in case val of
       B b -> return' (B b)
       I b -> return' (I b)
       A vs -> do
         vs' <- mapM expandTypeVal vs
         return' (A vs')
       S elems -> do
         let (ns, vs) = unzip elems
         vs' <- mapM expandTypeExp vs
         return' (S $ zip ns vs')
  
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
