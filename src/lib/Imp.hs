-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Imp (toImpFunction, impExprType) where

import Control.Monad.Reader
import Control.Monad.Except hiding (Except)
import Control.Monad.State
import Control.Monad.Writer
import Data.Foldable
import Data.Functor.Reverse
import Data.Text.Prettyprint.Doc

import Array
import Syntax
import Env
import Type
import PPrint
import Cat
import Subst
import Record
import Util (bindM2)

type EmbedEnv = ([IVar], (Scope, ImpProg))
type ImpM = ReaderT (Env IAtom) (Cat EmbedEnv)

type ScalarVar = VarP BaseType
type RefVar    = VarP IArrayType

data IAtom = IAVar ScalarVar
           | IALit LitVal
           | IASumCon IAtom IAtom IAtom
           | IARecCon (Record IAtom)
           | IADest IDest
             deriving Show

-- Atoms that can be used as a destination for writes
data IDest = IDVar RefVar
           | IDSumCon IDest IDest IDest
           | IDRecCon (Record IDest)
           | IDTabCon IDest
             deriving Show

toImpFunction :: ([Var], Expr) -> ImpFunction
toImpFunction (vsIn, expr) = runImpM $ do
  (vsOut, prog) <- scopedBlock $ materializeResult
  let arrIn  = flip fmap vsIn  (\(v :> ArrayTy b)        -> v :> b)
  let arrOut = flip fmap vsOut (\(v :> IRefType (_, b))  -> v :> b)
  return $ ImpFunction arrOut arrIn prog
  where
    materializeResult = do
      ans <- toImpExpr expr
      (outDest, vsOut) <- allocDest Unmanaged $ getType expr
      copyAtom outDest ans
      return vsOut

runImpM :: ImpM a -> a
runImpM m = fst $ runCat (runReaderT m mempty) mempty

toImpExpr :: Expr -> ImpM IAtom
toImpExpr expr = case expr of
  Decl (Let b bound) body -> do
    ans <- toImpCExpr bound
    extendR (b @> ans) $ toImpExpr body
  CExpr op  -> toImpCExpr op
  Atom atom -> fromAtom atom -- impSubst env atom

toImpCExpr :: CExpr -> ImpM IAtom
toImpCExpr op = case op of
  --TabCon n _ rows -> do
    --dest <- alloc resultTy
    --forM_ (zip [0..] rows) $ \(i, row) -> do
      --i' <- intToIndex n $ IIntVal i
      --ithDest <- impTabGet dest i'
      --copyAtom ithDest row
    --return dest
  For d (LamExpr b@(_:>idxTy) body) -> do
    n'   <- indexSetSize idxTy
    dest <- alloc resultTy
    emitLoop d n' $ \i -> do
      i'  <- intToIndex idxTy i
      ans <- extendR (b @> i') $ toImpExpr body
      ithDest <- impTabGet dest i
      copyAtom ithDest ans
    return $ IADest dest
  --TabGet x i -> impTabGet x i
  --SumGet x getLeft ->
    --case x of
      --SumVal _ l r -> return $ if getLeft then l else r
      --val -> error $ "Expected a sum type, got: " ++ pprint val
  --SumTag x ->
    --case x of
      --SumVal t _ _ -> return t
      --val -> error $ "Expected a sum type, got: " ++ pprint val
  --RecGet x i -> do
    --case x of
      --RecVal r -> return $ recGet r i
      --val -> error $ "Expected a record, got: " ++ pprint val
  --RunReader r (LamExpr ref body, env) -> do
    --toImpExpr (env <> ref @> L r) body
  --RunWriter (LamExpr ref body, env) -> do
    --wDest <- alloc wTy
    --initializeAtomZero wDest
    --aResult <- toImpExpr (env <> ref @> L wDest) body
    --return $ PairVal aResult wDest
    --where (PairTy _ wTy) = resultTy
  --RunState s (LamExpr ref body, env) -> do
    --sDest <- alloc sTy
    --copyAtom sDest s
    --aResult <- toImpExpr (env <> ref @> L sDest) body
    --return $ PairVal aResult sDest
    --where (PairTy _ sTy) = resultTy
  --IndexEff _ ref i (LamExpr b body, env) -> do
    --ref' <- impTabGet ref i
    --toImpExpr (env <> b @> L ref') body
  --PrimEffect ref m -> do
    --case m of
      --MAsk    -> return ref
      --MTell x -> addToAtom ref x >> return UnitVal
      --MPut x  -> copyAtom  ref x >> return UnitVal
      --MGet -> do
        --dest <- alloc resultTy
        --copyAtom dest ref
        --return dest
  --IntAsIndex n i -> do
    --i' <- fromScalarAtom i
    --n' <- indexSetSize n
    --ans <- emitInstr $ IPrimOp $
             --FFICall "int_to_index_set" [IntType, IntType] IntType [i', n']
    --return $ toScalarAtom resultTy ans
  --Cmp _ _ _ _ -> error $ "All instances of Cmp should get resolved in simplification"
  --IdxSetSize n -> liftM (toScalarAtom resultTy) $ indexSetSize n
  --IndexAsInt i -> toScalarAtom IntTy <$> indexToInt (getType i) i
  --Inject e -> do
    --let rt@(TC (IndexRange t low _)) = getType e
    --offset <- case low of
      --InclusiveLim a -> indexToInt t a
      --ExclusiveLim a -> indexToInt t a >>= impAdd IOne
      --Unlimited      -> return IZero
    --restrictIdx <- indexToInt rt e
    --idx <- impAdd restrictIdx offset
    --intToIndex t idx
  --_ -> do
    --op' <- traverseExpr op (return . toImpBaseType) fromScalarAtom (const (return ()))
    --liftM (toScalarAtom resultTy) $ emitInstr (IPrimOp op')
  _ -> undefined
  where
    resultTy :: Type
    resultTy = getType $ CExpr op

--toScalarAtom :: Type -> IExpr -> Atom
--toScalarAtom _  (ILit v) = Con $ Lit v
--toScalarAtom ty x@(IVar (v:>_)) = case ty of
  --BaseTy _                -> Var (v:>ty)
  --TC (IntRange       _ _) -> Con $ AsIdx ty $ toScalarAtom IntTy x
  --TC (IndexRange ty' _ _) -> Con $ AsIdx ty $ toScalarAtom ty' x
  --_ -> error $ "Not a scalar type: " ++ pprint ty

anyValue :: Type -> LitVal
anyValue (TC (BaseType RealType))   = RealLit 1.0
anyValue (TC (BaseType IntType))    = IntLit 1
anyValue (TC (BaseType BoolType))   = BoolLit False
anyValue (TC (BaseType StrType))    = StrLit ""
-- XXX: This is not strictly correct, because those types might not have any
--      inhabitants. We might want to consider emitting some run-time code that
--      aborts the program if this really ends up being the case.
anyValue (TC (IntRange _ _))        = IntLit 0
anyValue (TC (IndexRange _ _ _))    = IntLit 0
anyValue t = error $ "Expected a scalar type in anyValue, got: " ++ pprint t

fromAtom :: Atom -> ImpM IAtom
fromAtom a = case a of
  Var v -> asks (! v)
  Con con -> case con of
    AGet (Var (v :> ArrayTy b)) -> return $ IADest $ IDVar (v :> ([], b))
    Lit x      -> return $ IALit x
    AsIdx _ x  -> fromAtom x
    AnyValue t -> return $ IALit $ anyValue t
    RecCon r   -> IARecCon <$> traverse fromAtom r
    SumCon _ _ _ -> undefined
    AFor n x   -> do
      dims <- (n `extendDims` [])
      IADest . IDTabCon <$> fromDestAtom dims x
    _ -> error $ "Atom impossible to translate into an IAtom: " ++ show a
  _ -> error $ "Atom impossible to translate into an IAtom: " ++ show a

fromDestAtom :: [IDimType] -> Atom -> ImpM IDest
fromDestAtom = undefined

data AllocType = Managed | Unmanaged

alloc :: Type -> ImpM IDest
alloc ty = fst <$> allocDest Managed ty

allocDest :: AllocType -> Type -> ImpM (IDest, [IVar])
allocDest allocTy ty = do
  (dest, vs) <- makeDest "v" ty
  flip mapM_ vs $ \v@(_:>IRefType refTy) -> emitStatement (Just v, Alloc refTy)
  case allocTy of
    Managed   -> extend $ asFst vs
    Unmanaged -> return ()
  return (dest, vs)

makeDest :: Name -> Type -> ImpM (IDest, [IVar])
makeDest name ty = runWriterT $ makeDest' name [] ty

-- TODO: Handle more complicated index sets (possibly emit IPrecomputed instead of IUniform)
extendDims :: Type -> [IDimType] -> ImpM [IDimType]
extendDims t dims = case t of
  (TC (IntRange _ _))     -> uniform
  (TC (IndexRange _ _ _)) -> case dims of
    [] -> uniform
    _  -> error $ "IndexRanges only supported in the outermost array dimension"
  (RecTy rec) -> do
    newDims <- traverse (flip extendDims dims) $ toList rec
    appendUniform <$> (impProd $ fmap (\(IUniform sz:_) -> sz) newDims)
  (SumTy l r) -> do
    ~(IUniform l':_) <- extendDims l dims
    ~(IUniform r':_) <- extendDims r dims
    appendUniform <$> impAdd l' r'
  _           -> error "Missing a case for an index set type"
  where
    appendUniform sz = dims ++ [IUniform sz]
    uniform = appendUniform <$> (scalarToIExpr =<< indexSetSize t)

makeDest' :: Name -> [IDimType] -> Type -> WriterT [IVar] ImpM IDest
makeDest' name dims (TabTy n b) = do
  newDims <- lift $ n `extendDims` dims
  IDTabCon <$> makeDest' name newDims b
makeDest' name dims ty@(TC con) = case con of
  BaseType b -> do
    v <- lift $ freshVar (name :> IRefType (dims, b))
    tell [v]
    return $ IDVar $ varName v :> (dims, b)
  RecType r -> IDRecCon <$> traverse (makeDest' name dims) r
  SumType _ -> undefined
  IntRange   _ _   -> scalarIndexSet
  IndexRange _ _ _ -> scalarIndexSet
  _ -> error $ "Can't lower type to imp: " ++ pprint con
  where
    scalarIndexSet = makeDest' name dims IntTy
makeDest' _ _ ty = error $ "Can't lower type to imp: " ++ pprint ty

refToIExpr :: RefVar -> IExpr
refToIExpr (v :> arrTy) = IVar $ v :> IRefType arrTy

iExprToRef :: IExpr -> RefVar
iExprToRef (IVar (v :> IRefType arrTy)) = v :> arrTy
iExprToRef _ = error $ "Not a reference"

scalarToIExpr :: IAtom -> ImpM IExpr
scalarToIExpr a = case a of
  IAVar (v :> b) -> return $ IVar (v :> IValType b)
  IALit l        -> return $ ILit l
  IADest (IDVar ref@(_ :> ([], _))) -> load $ refToIExpr ref
  _              -> error $ "Not a scalar IAtom!"

iExprToScalar :: IExpr -> IAtom
iExprToScalar e = case e of
  IVar (v :> IValType b) -> IAVar $ v :> b
  ILit x                 -> IALit $ x
  _              -> error $ "Not a scalar IExpr!"

impTabGet :: IDest -> IAtom -> ImpM IDest
impTabGet (IDTabCon d) i = do
  i' <- scalarToIExpr i
  traverseRefs d $ \v -> do
    iExprToRef <$> (emitInstr $ IGet (refToIExpr v) i')
impTabGet _ _ = error "Expected an array atom in impTabGet"

intToIndex :: Type -> IAtom -> ImpM IAtom
intToIndex ty@(TC con) i = case con of
  IntRange _ _      -> return i
  IndexRange _ _ _  -> return i
  BaseType BoolType -> iExprToScalar <$> (emitUnOp UnsafeIntToBool =<< scalarToIExpr i)
  --RecType r -> do
    --strides <- getStrides $ fmap (\t->(t,t)) r
    --liftM RecVal $
      --flip evalStateT i $ forM strides $ \(ty', _, stride) -> do
        --i' <- get
        --iCur  <- lift $ impDiv i' stride
        --iRest <- lift $ impRem i' stride
        --put iRest
        --lift $ intToIndex ty' iCur
  --SumType (l, r) -> do
    --ls <- indexSetSize l
    --isLeft <- impCmp Less i ls
    --li <- intToIndex l i
    --ri <- intToIndex r =<< impSub i ls
    --return $ Con $ SumCon (toScalarAtom BoolTy isLeft) li ri
  _ -> error $ "Unexpected type " ++ pprint con
  --where
    --iAsIdx = return $ Con $ AsIdx ty $ impExprToAtom i
intToIndex ty _ = error $ "Unexpected type " ++ pprint ty

indexToInt :: Type -> IAtom -> ImpM IAtom
indexToInt ty idx = undefined --case ty of
  --BoolTy  -> emitUnOp BoolToInt =<< fromScalarAtom idx
  --RecTy rt -> do
    --case idx of
      --(RecVal rv) -> do
        --rWithStrides <- getStrides $ recZipWith (,) rv rt
        --foldrM f (IIntVal 0) rWithStrides
        --where
        --f :: (Atom, Type, IExpr) -> IExpr -> ImpM IExpr
        --f (i, it, stride) cumIdx = do
          --i' <- indexToInt it i
          --iDelta  <- impMul i' stride
          --impAdd cumIdx iDelta
      --_ -> error $ "Expected a record, got: " ++ pprint idx
  --SumTy lType rType     -> do
    --case idx of
      --(SumVal con lVal rVal) -> do
        --lTypeSize <- indexSetSize lType
        --lInt <- indexToInt lType lVal
        --rInt <- impAdd lTypeSize =<< indexToInt rType rVal
        --conExpr <- fromScalarAtom con
        --impSelect conExpr lInt rInt
      --_ -> error $ "Expected a sum constructor, got: " ++ pprint idx
  --TC (IntRange _ _)     -> fromScalarAtom idx
  --TC (IndexRange _ _ _) -> fromScalarAtom idx
  --_ -> error $ "Unexpected type " ++ pprint ty

getStrides :: Traversable f => f (a, Type) -> ImpM (f (a, Type, IExpr))
getStrides xs = undefined
  --liftM getReverse $ flip evalStateT (IIntVal 1) $
    --forM (Reverse xs) $ \(x, ty) -> do
      --stride  <- get
      --size    <- lift $ indexSetSize ty
      --stride' <- lift $ impMul stride size
      --put stride'
      --return (x, ty, stride)

--impExprToAtom :: IExpr -> Atom
--impExprToAtom e = case e of
  --IVar (v:>ty) -> Var (v:> impTypeToType ty)
  --ILit x       -> Con $ Lit x

--impTypeToType :: IType -> Type
--impTypeToType (IValType b)     = BaseTy b
--impTypeToType (IRefType arrTy) = TC $ IArrayType arrTy

--toImpBaseType :: Type -> BaseType
--toImpBaseType (TabTy _ a) = toImpBaseType a
--toImpBaseType (TC con) = case con of
  --BaseType b       -> b
  --IntRange _ _     -> IntType
  --IndexRange _ _ _ -> IntType
  --_ -> error $ "Unexpected type: " ++ pprint con
--toImpBaseType ty = error $ "Unexpected type: " ++ pprint ty

indexSetSize :: Type -> ImpM IAtom
indexSetSize (TC con) = case con of
  IntRange low high -> do
    low'  <- fromAtom low
    high' <- fromAtom high
    iaSub high' low'
  --IndexRange n low high -> do
    --low' <- case low of
      --InclusiveLim x -> indexToInt n x
      --ExclusiveLim x -> indexToInt n x >>= impAdd IOne
      --Unlimited      -> return IZero
    --high' <- case high of
      --InclusiveLim x -> indexToInt n x >>= impAdd IOne
      --ExclusiveLim x -> indexToInt n x
      --Unlimited      -> indexSetSize n
    --impSub high' low'
  --RecType r -> do
    --sizes <- traverse indexSetSize r
    --impProd $ toList sizes
  --BaseType BoolType -> return $ IIntVal 2
  --SumType (l, r) -> bindM2 impAdd (indexSetSize l) (indexSetSize r)
  --_ -> error $ "Not implemented " ++ pprint con
indexSetSize ty = error $ "Not implemented " ++ pprint ty

traverseRefs :: Applicative m => IDest -> (RefVar -> m RefVar) -> m IDest
traverseRefs dest f = case dest of
  IDVar v        -> IDVar    <$> f v
  IDTabCon d     -> IDTabCon <$> rec d
  IDSumCon t l r -> IDSumCon <$> rec t <*> rec l <*> rec r
  IDRecCon r     -> IDRecCon <$> traverse rec r
  where rec d = traverseRefs d f

refList :: IDest -> [RefVar]
refList dest = execWriter $ traverseRefs dest $ \v -> tell [v] >> return v

copyAtom :: IDest -> IAtom -> ImpM ()
copyAtom dest src = case (dest, src) of
  (_, IADest srcDest)                 -> zipWithM_ copyRef (refList dest) (refList srcDest)
    where copyRef d s = copy (refToIExpr d) (refToIExpr s)
  (IDRecCon destRec, IARecCon srcRec) -> zipWithM_ copyAtom (toList destRec) (toList srcRec)
  (IDSumCon _ _ _, IASumCon _ _ _)    -> undefined
  (IDVar v@(_ :> ([], _)), src) -> do
    store (refToIExpr v) =<< scalarToIExpr src
  _ -> error $ "Mismatch in copyAtom: " ++ show dest ++ " := " ++ show src

--initializeAtomZero :: Atom -> ImpM ()
--initializeAtomZero x = void $ flip traverseLeaves x $ \(~leaf@((Con (AGet dest)))) dims ->
  --fromArrayAtom dest dims >>= initializeZero >> return leaf

--addToAtom :: Atom -> Atom -> ImpM ()
--addToAtom dest src = bindM2 (zipWithM_ addToAtomLeaf) (leavesList dest) (leavesList src)

--addToAtomLeaf :: (Atom, [IDimType]) -> (Atom, [IDimType]) -> ImpM ()
--addToAtomLeaf (~(Con (AGet dest)), destDims) (src, srcDims) = case src of
  --Con (AGet src') -> bindM2 addToDestFromRef dest' (fromArrayAtom src' srcDims)
  --_               -> bindM2 addToDestScalar  dest' (fromScalarAtom src)
  --where dest' = fromArrayAtom dest destDims

-- === Imp embedding ===

iaSub :: IAtom -> IAtom -> ImpM IAtom
iaSub x y = iExprToScalar <$> bindM2 impSub (scalarToIExpr x) (scalarToIExpr y)

impProd :: [IExpr] -> ImpM IExpr
impProd []     = return $ IOne
impProd (x:xs) = foldrM impMul x xs

emitUnOp :: ScalarUnOp -> IExpr -> ImpM IExpr
emitUnOp op x = emitInstr $ IPrimOp $ ScalarUnOp op x

emitBinOp :: ScalarBinOp -> IExpr -> IExpr -> ImpM IExpr
emitBinOp op x y = emitInstr $ IPrimOp $ ScalarBinOp op x y

impAdd :: IExpr -> IExpr -> ImpM IExpr
impAdd IZero y = return y
impAdd x IZero = return x
impAdd (IIntVal x) (IIntVal y) = return $ IIntVal $ x + y
impAdd x y = emitBinOp IAdd x y

impMul :: IExpr -> IExpr -> ImpM IExpr
impMul IOne y = return y
impMul x IOne = return x
impMul (IIntVal x) (IIntVal y) = return $ IIntVal $ x * y
impMul x y = emitBinOp IMul x y

impDiv :: IExpr -> IExpr -> ImpM IExpr
impDiv x IOne = return x
impDiv x y = emitBinOp IDiv x y

impRem :: IExpr -> IExpr -> ImpM IExpr
impRem _ IOne = return IZero
impRem x y = emitBinOp Rem x y

impSub :: IExpr -> IExpr -> ImpM IExpr
impSub (IIntVal a) (IIntVal b)  = return $ IIntVal $ a - b
impSub a IZero = return a
impSub x y = emitBinOp ISub x y

impCmp :: CmpOp -> IExpr -> IExpr -> ImpM IExpr
impCmp GreaterEqual (IIntVal a) (IIntVal b) = return $ ILit $ BoolLit $ a >= b
impCmp op x y = emitBinOp (ICmp op) x y

-- Precondition: x and y don't have array types
impSelect :: IExpr -> IExpr -> IExpr -> ImpM IExpr
impSelect p x y = emitInstr $ IPrimOp $ Select t p x y
  where (IValType t) = impExprType x

copy :: IExpr -> IExpr -> ImpM ()
copy dest src = emitStatement (Nothing, Copy dest src)

load :: IExpr -> ImpM IExpr
load x = emitInstr $ Load x

castArray :: Var -> [IDimType] -> ImpM IExpr
castArray v@(_:>(ArrayTy b)) dims = emitInstr $ CastArray v (dims, b)
castArray _ _ = error "Expected an array in castArray"

store :: IExpr -> IExpr -> ImpM ()
store dest src = emitStatement (Nothing, Store dest src)

freshVar :: VarP a -> ImpM (VarP a)
freshVar v = do
  scope <- looks (fst . snd)
  let v' = rename v scope
  extend $ asSnd $ asFst (v' @> ())
  return v'

emitLoop :: Direction -> IAtom -> (IAtom -> ImpM ()) -> ImpM ()
emitLoop d n body = do
  n' <- scalarToIExpr n
  (i, loopBody) <- scopedBlock $ do
    i <- freshVar ("i" :> IValType IntType)
    body $ IAVar $ varName i :> IntType
    return i
  emitStatement (Nothing, Loop d i n' loopBody)

scopedBlock :: ImpM a -> ImpM (a, ImpProg)
scopedBlock body = do
  (ans, (allocs, (scope', prog))) <- scoped body
  extend (mempty, (scope', mempty))  -- Keep the scope extension to avoid reusing variable names
  let frees = ImpProg [(Nothing, Free v) | v <- allocs]
  return (ans, prog <> frees)

emitStatement :: ImpStatement -> ImpM ()
emitStatement statement = extend $ asSnd $ asSnd $ ImpProg [statement]

emitInstr :: ImpInstr -> ImpM IExpr
emitInstr instr = do
  case ignoreExcept (instrType instr) of
    Just ty -> do
      v <- freshVar ("v":>ty)
      emitStatement (Just v, instr)
      return $ IVar v
    Nothing -> error "Expected non-void result"

--addToDestFromRef :: IExpr -> IExpr -> ImpM ()
--addToDestFromRef dest src = case impExprType dest of
  --IRefType ([], RealType) -> do
    --cur  <- load dest
    --src' <- load src
    --updated <- emitInstr $ IPrimOp $ ScalarBinOp FAdd cur src'
    --store dest updated
  --IRefType ((dim:_), RealType) ->
    --emitLoop Fwd (dimSize dim) $ \i -> do
      --dest' <- emitInstr $ IGet dest i
      --src'  <- emitInstr $ IGet src  i
      --addToDestFromRef dest' src'
  --ty -> error $ "Addition not implemented for type: " ++ pprint ty

--addToDestScalar :: IExpr -> IExpr -> ImpM ()
--addToDestScalar dest src = do
  --cur  <- load dest
  --updated <- emitInstr $ IPrimOp $ ScalarBinOp FAdd cur src
  --store dest updated

--initializeZero :: IExpr -> ImpM ()
--initializeZero ref = case impExprType ref of
  --IRefType ([],    RealType)   -> store ref (ILit (RealLit 0.0))
  --IRefType ((dim:_), RealType) ->
    --emitLoop Fwd (dimSize dim) $ \i -> emitInstr (IGet ref i) >>= initializeZero
  --ty -> error $ "Zeros not implemented for type: " ++ pprint ty

--dimSize :: IDimType -> IExpr
--dimSize dimTy = case dimTy of
  --IUniform s -> s
  --IPrecomputed (_ :> IRefType ([IUniform s], _)) -> s
  --_ -> error $ "Unexpected dim type in dimSize: " ++ pprint dimTy

-- === type checking imp programs ===

-- State keeps track of _all_ names used in the program, Reader keeps the type env.
type ImpCheckM a = StateT Scope (ReaderT (Env IType) (Either Err)) a

instance Checkable ImpFunction where
  checkValid (ImpFunction _ vsIn (ImpProg prog)) = do
    let scope = foldMap (varAsEnv . fmap (const ())) vsIn
    void $ runReaderT (runStateT (checkProg prog) scope) mempty

checkProg :: [ImpStatement] -> ImpCheckM ()
checkProg [] = return ()
checkProg ((maybeBinder, instr):prog) = do
  maybeTy <- instrTypeChecked instr
  case (maybeBinder, maybeTy) of
    (Nothing, Nothing) -> checkProg prog
    (Nothing, Just _ ) -> throw CompilerErr $ "Result of non-void instruction must be assigned"
    (Just _ , Nothing) -> throw CompilerErr $ "Can't assign result of void instruction"
    (Just v@(_:>ty), Just ty') -> do
      checkBinder v
      checkValidType ty
      assertEq ty ty' "Type mismatch in instruction"
      extendR (v@>ty) $ checkProg prog

instrTypeChecked :: ImpInstr -> ImpCheckM (Maybe IType)
instrTypeChecked instr = case instr of
  IPrimOp op -> liftM Just $ checkImpOp op
  Load ref -> do
    b <- (checkIExpr >=> fromScalarRefType) ref
    return $ Just $ IValType b
  Store dest val -> do
    b <- (checkIExpr >=> fromScalarRefType) dest
    valTy <- checkIExpr val
    assertEq (IValType b) valTy "Type mismatch in store"
    return Nothing
  Copy dest source -> do
    _ <- (checkIExpr >=> fromRefType) dest
    _ <- (checkIExpr >=> fromRefType) source
    -- FIXME: Reenable this check!
    --assertEq sourceTy destTy "Type mismatch in copy"
    return Nothing
  CastArray v (dims, b) -> case v of
    _ :> ArrayTy b' -> do
      env <- get
      when (not $ v `isin` env) $ throw CompilerErr $ "Unbound array variable: " ++ pprint v
      assertEq b b' "Type mismatch in cast array"
      return $ Just $ IRefType (dims, b)
    _ -> throw CompilerErr $ "Casting a non-array variable to array"
  Alloc ty -> return $ Just $ IRefType ty
  Free _   -> return Nothing  -- TODO: check matched alloc/free
  Loop _ i size (ImpProg block) -> do
    checkInt size
    checkBinder i
    extendR (i @> IIntTy) $ checkProg block
    return Nothing
  IGet e i -> do
    ~(IRefType ((_:dims), b)) <- checkIExpr e
    checkInt i
    return $ Just $ IRefType (dims, b)

checkBinder :: IVar -> ImpCheckM ()
checkBinder v = do
  env <- get
  when (v `isin` env) $ throw CompilerErr $ "shadows: " ++ pprint v
  modify (<>(v@>()))

checkValidType :: IType -> ImpCheckM ()
checkValidType (IValType _        ) = return ()
checkValidType (IRefType (dims, _)) = mapM_ checkDimType dims

checkDimType :: IDimType -> ImpCheckM ()
checkDimType dimTy = case dimTy of
  IUniform sz -> checkInt sz
  IPrecomputed (_ :> IRefType ([IUniform sz], IntType)) -> checkInt sz
  IPrecomputed _ -> throw CompilerErr $ "Unexpected precomputed stride array type: " ++ pprint dimTy

checkIExpr :: IExpr -> ImpCheckM IType
checkIExpr expr = case expr of
  ILit val -> return $ IValType (litType val)
  -- TODO: check shape matches vector length
  IVar v -> asks $ (! v)

checkInt :: IExpr -> ImpCheckM ()
checkInt expr = do
  ty <- checkIExpr expr
  assertEq (IValType IntType) ty $ "Not an int: " ++ pprint expr

checkImpOp :: IPrimOp -> ImpCheckM IType
checkImpOp op = do
  op' <- traverseExpr op
           return
           (\x  -> checkIExpr x)
           (error "shouldn't have lambda")
  case op' of
    ScalarBinOp scalarOp x y -> do
      checkEq x (IValType x')
      checkEq y (IValType y')
      return $ IValType ty
      where (x', y', ty) = binOpType scalarOp
    ScalarUnOp scalarOp x -> do
      checkEq x (IValType x')
      return $ IValType ty
      where (x', ty) = unOpType scalarOp
    Select ty _ x y -> do
      checkEq (IValType ty) x
      checkEq (IValType ty) y
      return $ IValType ty
    FFICall _ _ ty _   -> return $ IValType ty -- TODO: check
    _ -> error $ "Not allowed in Imp IR: " ++ pprint op
  where
    checkEq :: (Pretty a, Eq a) => a -> a -> ImpCheckM ()
    checkEq t t' = assertEq t t' (pprint op)

fromRefType :: MonadError Err m => IType -> m IArrayType
fromRefType (IRefType ty) = return ty
fromRefType ty = throw CompilerErr $ "Not a reference type: " ++ pprint ty

fromScalarRefType :: MonadError Err m => IType -> m BaseType
fromScalarRefType (IRefType ([], b)) = return b
fromScalarRefType ty = throw CompilerErr $ "Not a scalar reference type: " ++ pprint ty

impExprType :: IExpr -> IType
impExprType expr = case expr of
  ILit v    -> IValType (litType v)
  IVar (_:>ty) -> ty

instrType :: MonadError Err m => ImpInstr -> m (Maybe IType)
instrType instr = case instr of
  IPrimOp op      -> return $ Just $ impOpType op
  Load ref        -> liftM (Just . IValType) $ fromScalarRefType (impExprType ref)
  Store _ _       -> return Nothing
  Copy  _ _       -> return Nothing
  CastArray _ ty  -> return $ Just $ IRefType ty
  Alloc ty        -> return $ Just $ IRefType ty
  Free _          -> return Nothing
  Loop _ _ _ _    -> return Nothing
  IGet e _        -> case impExprType e of
    IRefType ((_:dims), b) -> return $ Just $ IRefType (dims, b)
    ty -> error $ "Can't index into: " ++ pprint ty


impOpType :: IPrimOp -> IType
impOpType (ScalarBinOp op _ _) = IValType ty  where (_, _, ty) = binOpType op
impOpType (ScalarUnOp  op _  ) = IValType ty  where (_,    ty) = unOpType  op
impOpType (Select ty _ _ _   ) = IValType ty
impOpType (FFICall _ _ ty _  ) = IValType ty
impOpType op = error $ "Not allowed in Imp IR: " ++ pprint op

pattern IIntTy :: IType
pattern IIntTy = IValType IntType

pattern IIntVal :: Int -> IExpr
pattern IIntVal x = ILit (IntLit x)

pattern IZero :: IExpr
pattern IZero = IIntVal 0

pattern IOne :: IExpr
pattern IOne = IIntVal 1
