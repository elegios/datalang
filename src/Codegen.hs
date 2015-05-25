{-# LANGUAGE TupleSections, TemplateHaskell, LambdaCase, TypeSynonymInstances, FlexibleInstances, OverloadedStrings #-}

module CodeGen (generate) where

import GlobalAst (Inline(..), getSizeFromTSize, nowhere, TerminatorType(..), BinOp(..), UnOp(..), TSize(..))
import NameResolution.Ast (Resolved(..))
import Inference.Ast (TypeKey, FlatType(..), CallableDef, CallableDefT(..), Statement, StatementT(..), Expression, ExpressionT(..), Literal(..), bool, CompoundAccess(..), representation, Default(..))
import Control.Applicative ((<*>), Applicative)
import Control.Lens hiding (op, index)
import Control.Monad.State
import Control.Monad.Except (ExceptT, runExceptT, MonadError, throwError)
import Data.Either (partitionEithers)
import Data.Maybe (fromMaybe)
import Data.Functor ((<$>))
import Data.List (find)
import Data.Word (Word32, Word)
import Data.String (IsString, fromString)
import Data.Tuple (swap)
import GHC.Float (double2Float)
import LLVM.General.AST (Name(..), Type(..), BasicBlock(..))
import LLVM.General.AST.Instruction hiding (index)
import qualified Data.Map as M
import qualified Data.Traversable as T
import qualified LLVM.General.AST as AST
import qualified LLVM.General.AST.Global as G
import qualified LLVM.General.AST.Attribute as A
import qualified LLVM.General.AST.Type as T
import qualified LLVM.General.AST.CallingConvention as CC
import qualified LLVM.General.AST.Constant as C
import qualified LLVM.General.AST.Linkage as Linkage
import qualified LLVM.General.AST.Visibility as Visibility
import qualified LLVM.General.AST.IntegerPredicate as IP
import qualified LLVM.General.AST.FloatingPointPredicate as FP
import qualified LLVM.General.AST.Float as F

data ErrorMessage = ErrorString String deriving Show

type CodeGen a = StateT CodeGenState (ExceptT ErrorMessage Identity) a
type Super a = StateT SuperState Identity a

data CodeGenState = CodeGenState
                    { _super :: SuperState
                    , _fresh :: Word
                    , _locals :: M.Map Resolved Operand
                    , _entryBlock :: BasicBlock
                    , _currentBlock :: BasicBlock
                    , _finalizedBlocks :: [BasicBlock]
                    , _retInstr :: Named Terminator
                    , _defers :: Defers
                    , _breakTarget :: Maybe Name
                    , _continueTarget :: Maybe Name
                    , _replacementContext :: Operand
                    }
data Defers = Defers
              { _defersAll :: [Statement]
              , _defersLoop :: [Statement]
              , _defersScope :: [Statement]
              }

data SuperState = SuperState
                  { _callableNames :: M.Map (Resolved, TypeKey, Inline) Name
                  , _namedTypes :: M.Map TypeKey Type
                  , _types :: M.Map TypeKey FlatType
                  , _typeKeys :: M.Map FlatType TypeKey
                  , _structCounter :: Int
                  }

data Operand = Operand TypeKey Bool AST.Operand

class Generateable a where
  gen :: a -> CodeGen ()

class GenerateableWithOperand a where
  genO :: a -> CodeGen Operand

makeLenses ''CodeGenState
makeLenses ''SuperState
makeLenses ''Defers

generate :: [(CallableDef, M.Map TypeKey FlatType)] -> Either [ErrorMessage] AST.Module
generate inferred = runSuper $ do
  (errs, generated) <- partitionEithers <$> mapM genCallable inferred
  if null errs
    then Right <$> finishGeneration (makeDefMap generated)
    else return $ Left errs
  where
    runSuper = runIdentity . flip evalStateT initState
    initState = SuperState
                { _callableNames = M.empty
                , _namedTypes = M.empty
                , _types = M.empty
                , _typeKeys = M.empty
                , _structCounter = 0
                }
    getSig d = (Global $ callableName d, finalType d)
    makeDefMap = M.fromList . zip (getSig . fst <$> inferred)

finishGeneration :: M.Map (Resolved, TypeKey) AST.Global -> Super AST.Module
finishGeneration fdefs = do
  functionDefs <- map makeF . M.toList <$> use callableNames
  (nts, fts) <- unzip . M.elems
                <$> (M.intersectionWith (,) <$> use namedTypes <*> use types)
  llvmts <- mapM fToLLVMType fts
  let typeDefs = zipWith makeT nts llvmts
      makeT (NamedTypeReference n) t = AST.TypeDefinition n $ Just t
  return $ AST.defaultModule { AST.moduleDefinitions = functionDefs ++ typeDefs }
  where
    makeF ((r, t, i), n) = case M.lookup (r, t) fdefs of
      Nothing -> error $ "Compiler error, couldn't find function " ++ show (r, t)
      Just f@G.Function{G.functionAttributes = attrs} -> AST.GlobalDefinition $ case i of
        NeverInline -> f { G.name = n, G.functionAttributes = A.NoInline : attrs }
        UnspecifiedInline -> f { G.name = n }
        AlwaysInline -> f { G.name = n, G.functionAttributes = A.AlwaysInline : attrs }

-- ###Callable generation starters

genCallable :: (CallableDef, M.Map TypeKey FlatType) -> Super (Either ErrorMessage AST.Global)
genCallable (d, ts) = do
  prevTypes <- types <<.= ts
  typeKeys .= M.fromList (map swap $ M.toList ts) -- TODO: possibly a more performant way to do this
  let newToName = M.keys . M.filter isStruct $ M.difference ts prevTypes
  firstN <- structCounter <<+= length newToName
  let newNamed = M.fromAscList $ zip newToName newNames
      newNames = NamedTypeReference . Name . ("struct" ++) . show <$> [firstN..]
  namedTypes %= (`M.union` newNamed)
  get >>= runCodeGen (codegenCallable d)
  where
    isStruct StructT{} = True
    isStruct _ = False
    runCodeGen m su = case run of
      Right (ret, CodeGenState{_super = st}) -> put st >> return (Right ret)
      Left e -> return $ Left e
      where
        run = runIdentity . runExceptT . runStateT m $ CodeGenState
              { _super = su
              , _fresh = 0
              , _entryBlock = BasicBlock "entry" [] (Do $ Br "first" [])
              , _currentBlock = BasicBlock "first" [] (Do $ Ret Nothing [])
              , _finalizedBlocks = []
              , _locals = M.empty
              , _retInstr = Do $ Ret Nothing []
              , _defers = Defers [] [] []
              , _breakTarget = Nothing
              , _continueTarget = Nothing
              , _replacementContext = error "Compiler error: a replacement context was used without being in one"
              }

codegenCallable :: CallableDef -> CodeGen AST.Global
codegenCallable d@FuncDef{} = do
  (ins, inps) <- fmap unzip . mapM (makeParamOp False) $ intypes d
  (out, _) <- makeParamOp True $ outtype d
  locals .= M.fromList (zip (outarg d : inargs d) (out : ins))

  retInstr .= (Do $ Br "return" [])
  currentBlock . blockTerminator .= (Do $ Br "return" [])
  gen initRet

  firstBlock <- currentBlock <<.= BasicBlock "return" [] undefined
  Operand _ _ op <- genO readRet >>= unPoint
  currentBlock . blockTerminator .= (Do $ Ret (Just op) [])
  finalizeAndReplaceWith firstBlock

  blocks <- codegenBody d
  retty <- toLLVMType False $ outtype d
  return $ defaultFunction
    { G.basicBlocks = blocks
    , G.parameters = (inps, False)
    , G.returnType = retty
    }
  where
    initRet :: Statement
    initRet = VarInit True (outarg d) (ExprLit (Zero (outtype d) nowhere)) nowhere
    readRet :: Expression
    readRet = Variable (outarg d) (outtype d) nowhere

codegenCallable d@ProcDef{} = do
  (ins, inps) <- fmap unzip . mapM (makeParamOp False) $ intypes d
  (outs, outps) <- fmap unzip . mapM (makeParamOp True) $ outtypes d
  locals .= M.fromList (zip (inargs d ++ outargs d) (ins ++ outs))

  blocks <- codegenBody d
  return $ defaultFunction
    { G.basicBlocks = blocks
    , G.parameters = (inps ++ outps, False)
    }

makeParamOp :: Bool -> TypeKey -> CodeGen (Operand, AST.Parameter)
makeParamOp pointable t = do
  n <- newName
  llvmt <- toLLVMType pointable t
  return ( Operand t pointable $ AST.LocalReference llvmt n
         , AST.Parameter llvmt n [])

codegenBody :: CallableDef -> CodeGen [BasicBlock]
codegenBody d = do
  gen $ callableBody d
  use currentBlock >>= finalizeBlock
  use entryBlock >>= finalizeBlock
  use finalizedBlocks

-- ###Regular code generation

instance Generateable Statement where
  gen (ProcCall inl (Variable n@Global{} pt _) is os _) = do
    pop <- requestCallable (n, pt, inl)
    iOps <- mapM (genO >=> unPoint) is
    oOps <- mapM genO os
    uinstr $ Call False CC.Fast [] pop ((,[]) . getOp <$> (iOps ++ oOps)) [] []
  gen (ProcCall _ e is os _) = do -- TODO: check if this is correct and actually works
    Operand _ False pop <- genO e >>= unPoint
    iOps <- mapM (genO >=> unPoint) is
    oOps <- mapM genO os
    uinstr $ Call False CC.Fast [] (Right pop) ((,[]) . getOp <$> (iOps ++ oOps)) [] []
  gen (Defer stmnt _) = do
    defers . defersAll %= (stmnt :)
    defers . defersLoop %= (stmnt :)
    defers . defersScope %= (stmnt :)
  gen (ShallowCopy a e _) = do
    Operand _ True aOp <- genO a -- TODO: throw error before codegen if fail
    Operand _ False eOp <- genO e >>= unPoint
    uinstr $ Store False aOp eOp Nothing 0 []
  gen (If cond stmnt mElseStmnt _) = do
    Operand _ _ condOp <- genO cond >>= unPoint
    (thenName, elseName, nextName) <- (,,) <$> newName <*> newName <*> newName
    prevTerminator <- currentBlock . blockTerminator <<.=
                      (Do $ CondBr condOp thenName elseName [])

    finalizeAndReplaceWith $ BasicBlock thenName [] (Do $ Br nextName [])
    gen stmnt

    finalizeAndReplaceWith $ BasicBlock elseName [] (Do $ Br nextName [])
    maybe (return ()) gen mElseStmnt

    finalizeAndReplaceWith $ BasicBlock nextName [] prevTerminator
  gen (While cond stmnt _) = do
    (condName, bodyName, nextName) <- (,,) <$> newName <*> newName <*> newName
    prevTerminator <- currentBlock . blockTerminator <<.= (Do $ Br condName [])

    finalizeAndReplaceWith $ BasicBlock condName [] undefined
    Operand _ False condOp <- genO cond >>= unPoint
    currentBlock . blockTerminator .= (Do $ CondBr condOp bodyName nextName [])

    finalizeAndReplaceWith $ BasicBlock bodyName [] (Do $ Br condName [])
    prevBreak <- breakTarget <<.= Just nextName
    prevContinue <- continueTarget <<.= Just condName
    gen stmnt
    breakTarget .= prevBreak
    continueTarget .= prevContinue

    finalizeAndReplaceWith $ BasicBlock nextName [] prevTerminator
  gen (Scope stmnts _) = do
    prevLocals <- use locals
    prevDefers <- use defers
    defers . defersScope .= []

    mapM_ gen stmnts

    use (defers . defersScope) >>= mapM_ gen
    defers .= prevDefers
    locals .= prevLocals
  gen (Terminator tt r) = do
    (term, deferred) <- case tt of
      Return -> (,) <$> use retInstr <*> use (defers . defersAll)
      _ -> do
        target <- use (boolean breakTarget continueTarget $ tt == Break) >>=
          justErr (ErrorString $ "Cannot break or continue at " ++ show r ++ ", no loop.")
        (Do $ Br target [], ) <$> use (defers . defersLoop)
    mapM_ gen deferred
    currentBlock . blockTerminator .= term
  gen (VarInit False n e _) = genO e >>= unPoint >>= (locals . at n ?=)
  gen (VarInit True n e _) = do
    Operand t False eOp <- genO e >>= unPoint
    allocaName <- newName
    allocaType <- toLLVMType False t
    let varOp = AST.LocalReference (T.ptr allocaType) allocaName
        alloca = Alloca allocaType Nothing 0 []
    entryBlock . blockInstrs %= (allocaName := alloca :)
    locals . at n ?= Operand t True varOp
    uinstr $ Store False varOp eOp Nothing 0 []

instance GenerateableWithOperand Expression where
  genO (Bin op e1 e2 _) = do
    Operand t1 False e1op <- genO e1 >>= unPoint
    if op `elem` [ShortAnd, ShortOr]
      then shortcutting t1 op e1op e2
      else genO e2 >>= unPoint >>= simpleBinOps t1 op e1op . getOp

  genO (Un AddressOf e _) = do
    Operand t True eOp <- genO e
    ptrT <- use (super . typeKeys . at (PointerT t)) >>= justErr (ErrorString $ "Compiler error: could not find the typekey for " ++ show (PointerT t))
    return $ Operand ptrT False eOp
  genO (Un Deref e _) = do
    Operand ptrT False eOp <- genO e >>= unPoint
    PointerT t <- getFT ptrT
    return $ Operand t True eOp
  genO (Un AriNegate e _) = do
    Operand t False eOp <- genO e >>= unPoint
    ft <- getFT t
    let instruction = case ft of
          FloatT{} -> FSub NoFastMathFlags
          _ -> Sub False False
        zero = case ft of
          FloatT S32 -> AST.ConstantOperand . C.Float $ F.Single 0
          FloatT S64 -> AST.ConstantOperand . C.Float $ F.Double 0
          _ -> AST.ConstantOperand $ C.Int (getSize ft) 0
    instr t False $ instruction zero eOp []
  genO (Un _ e _) = do -- NOTE: Not and BinNegate
    Operand t False eOp <- genO e >>= unPoint
    ft <- getFT t
    instr t False $ AST.Xor eOp (AST.ConstantOperand $ C.Int (getSize ft) (-1)) []

  genO (CompoundAccess e (ExpandedMember m) r) = do
    Operand t pointable eOp <- genO e
    StructT ps <- getFT t
    let (index, (_, it)) = fromMaybe err
                           (find ((m ==) . fst . snd) $ zip [(0::Integer)..] ps)
        con i = AST.ConstantOperand $ C.Int 32 i
        err = error $ "Compiler error: could not find member " ++ m ++ " at " ++ show r ++ ", ps was " ++ show ps
    instr it pointable $ if pointable
                         then GetElementPtr True eOp [con 0, con index] []
                         else ExtractValue eOp [fromInteger index] []
  genO (CompoundAccess ptr (ExpandedSubscript indexE) _) = do
    Operand ptrT False ptrOp <- genO ptr >>= unPoint
    PointerT it <- getFT ptrT
    Operand _ False indexOp <- genO indexE >>= unPoint
    -- TODO: extend indexT correctly depending on signedness
    instr it True $ GetElementPtr True ptrOp [indexOp] []
  genO (CompoundAccess e (Expanded repMap mCond repE) _) = do
    let (def, ext) = M.partition ((== Default) . fst) repMap
    prevLocals <- T.mapM (genO . snd) ext >>= (locals <<%=) . M.union
    prevContext <- genO e >>= (replacementContext <<.=)
    T.mapM (genO . snd) def >>= (locals %=) . M.union
    -- TODO: generate cond, set to explode or something
    ret <- genO repE
    locals .= prevLocals
    replacementContext .= prevContext
    return ret

  genO (Variable n t _) = case n of
    Self -> use replacementContext
    Global g -> undefined -- TODO: get a function pointer
    _ -> use (locals . at n) >>= justErr (ErrorString $ "Compiler error: could not find variable " ++ show n)
  genO (FuncCall inl (Variable n@Global{} ft _) is retty _) = do
    fOp <- requestCallable (n, ft, inl)
    iOps <- mapM (genO >=> unPoint) is
    instr retty False $ Call False CC.Fast [] fOp ((,[]) . getOp <$> iOps) [] []
  genO (FuncCall _ f is retty _) = do -- TODO: check if this is correct and actually works
    Operand _ False fOp <- genO f >>= unPoint
    iOps <- mapM (genO >=> unPoint) is
    instr retty False $ Call False CC.Fast [] (Right fOp) ((,[]) . getOp <$> iOps) [] []
  genO (ExprLit l) = genO l

instance GenerateableWithOperand Literal where
  genO (ILit val t _) = do
    ft <- getFT t
    return . Operand t False . AST.ConstantOperand $ C.Int (getSize ft) val
  genO (FLit val t _) = do
    ft <- getFT t
    return . Operand t False . AST.ConstantOperand . C.Float $ case ft of
      FloatT S64 -> F.Double val
      FloatT S32 -> F.Single $ double2Float val
  genO (BLit val _) = return $ if val then true else false
  genO (Null t _) =
    Operand t False . AST.ConstantOperand . C.Null <$> toLLVMType False t
  genO (Undef t _) =
    Operand t False . AST.ConstantOperand . C.Undef <$> toLLVMType False t
  genO (Zero t _) = Operand t False . AST.ConstantOperand <$> getZ t
    where
      getZ it = getFT it >>= \case
        FloatT S32 -> return . C.Float $ F.Single 0
        FloatT S64 -> return . C.Float $ F.Double 0
        PointerT _ -> C.Null <$> toLLVMType False t
        -- TODO: FuncT and ProcT, they have no zero types atm
        StructT ps -> do
          NamedTypeReference n <- toLLVMType False it
          C.Struct (Just n) False <$> mapM (getZ . snd) ps
        ft -> return $ C.Int (getSize ft) 0 -- NOTE: BoolT, IntT, UIntT
  genO (StructLit ps t _) = do
    start <- genO $ Undef t nowhere
    foldM genElement start $ zip [0..] ps
    where
      genElement (Operand _ _ prevOp) (index, e) = do
        Operand _ False eOp <- genO e >>= unPoint
        instr t False $ InsertValue prevOp eOp [index] []


shortcutting :: TypeKey -> BinOp -> AST.Operand -> Expression -> CodeGen Operand
shortcutting t op e1op e2 = do
  prevName <- use (currentBlock . blockName)
  (contName, nextName) <- (,) <$> newName <*> newName
  let (tNext, fNext) = case op of
        ShortAnd -> (contName, nextName)
        ShortOr -> (nextName, contName)
  prevTerminator <- currentBlock . blockTerminator <<.=
                    (Do $ CondBr e1op tNext fNext [])

  finalizeAndReplaceWith $ BasicBlock contName [] (Do $ Br nextName [])
  Operand _ _ e2op <- genO e2 >>= unPoint

  finalizeAndReplaceWith $ BasicBlock nextName [] prevTerminator
  instr t False $ Phi T.i1 [(e1op, prevName), (e2op, contName)] []

simpleBinOps :: TypeKey -> BinOp -> AST.Operand -> AST.Operand -> CodeGen Operand
simpleBinOps t op op1 op2 = do
  ft <- getFT t
  let floatSpec f nonF = case ft of
        FloatT{} -> f
        _ -> nonF
      threeSpec f u i = case ft of
        FloatT{} -> f
        UIntT{} -> u
        IntT{} -> i
      retty = if op `elem` [Lesser, Greater, LE, GE, Equal, NotEqual] then bool else t
      instruction = case op of
        Plus -> floatSpec (FAdd NoFastMathFlags) (Add False False)
        Minus -> floatSpec (FSub NoFastMathFlags) (Sub False False)
        Times -> floatSpec (FMul NoFastMathFlags) (Mul False False)
        Divide -> threeSpec (FAdd NoFastMathFlags) (UDiv False) (SDiv False)
        Remainder -> threeSpec (FRem NoFastMathFlags) URem SRem
        LongAnd -> And
        LongOr -> Or
        BinAnd -> And
        BinOr -> Or
        LShift -> Shl False False -- TODO: force the second operand to be unsigned in inferrence
        LogRShift -> LShr False -- TODO: as the line above
        AriRShift -> AShr False -- TODO: as the line above
        GlobalAst.Xor -> AST.Xor
        Lesser -> threeSpec (FCmp FP.OLT) (ICmp IP.ULT) (ICmp IP.SLT)
        Greater -> threeSpec (FCmp FP.OGT) (ICmp IP.UGT) (ICmp IP.SGT)
        LE -> threeSpec (FCmp FP.OLE) (ICmp IP.ULE) (ICmp IP.SLE)
        GE -> threeSpec (FCmp FP.OGE) (ICmp IP.UGE) (ICmp IP.SGE)
        Equal -> floatSpec (FCmp FP.OEQ) (ICmp IP.EQ)
        NotEqual -> floatSpec (FCmp FP.ONE) (ICmp IP.NE)
      (foldOp, startVal) = case op of
        Equal -> (And, true)
        NotEqual -> (Or, false)
      structCmpFold (Operand _ _ prev) (i, it) = do
        Operand _ _ m1op <- instr it False $ ExtractValue op1 [i] []
        Operand _ _ m2op <- instr it False $ ExtractValue op2 [i] []
        Operand _ _ nextOp <- simpleBinOps it op m1op m2op
        instr bool False $ foldOp prev nextOp []
  case ft of
    (StructT ps) -> foldM structCmpFold startVal . zip [0..] $ snd <$> ps
    _ -> instr retty False $ instruction op1 op2 []



-- ###Codegen helpers

true :: Operand
true = Operand bool False . AST.ConstantOperand $ C.Int 1 1
false :: Operand
false = Operand bool False . AST.ConstantOperand $ C.Int 1 0

uinstr :: Instruction -> CodeGen ()
uinstr instruction = currentBlock . blockInstrs %= (Do instruction :)

instr :: TypeKey -> Bool -> Instruction -> CodeGen Operand
instr tk pointable instruction = do
  n <- newName
  t <- toLLVMType pointable tk
  currentBlock . blockInstrs %= (n := instruction :)
  return . Operand tk pointable $ AST.LocalReference t n

requestCallable :: (Resolved, TypeKey, Inline) -> CodeGen AST.CallableOperand
requestCallable sig@(Global n, tk, inl) =
  use (super . callableNames . at sig) >>= \case
    Just n' -> do
      t <- toLLVMType False tk
      return . Right . AST.ConstantOperand $ C.GlobalReference t n'
    Nothing -> do
      t <- toLLVMType False tk
      n' <- makeName
      return . Right . AST.ConstantOperand $ C.GlobalReference t n'
  where
    makeName = super . callableNames . at sig <?= Name (n ++ "#" ++ show (representation tk) ++ "#" ++ (case inl of AlwaysInline -> "a"; UnspecifiedInline -> "u"; NeverInline -> "n"))

unPoint :: Operand -> CodeGen Operand
unPoint o@(Operand _ False _) = return o
unPoint (Operand t True prev) = instr t False $ Load False prev Nothing 0 []

getOp :: Operand -> AST.Operand
getOp (Operand _ _ o) = o

defaultFunction :: G.Global
defaultFunction = G.Function
  { G.linkage = Linkage.Internal
  , G.visibility = Visibility.Default
  , G.callingConvention = CC.Fast
  , G.returnAttributes = []
  , G.returnType = T.void
  , G.name = error "Compiler error: This function does not yet have a name set"
  , G.parameters = ([], False)
  , G.functionAttributes = []
  , G.section = Nothing
  , G.alignment = 0
  , G.garbageCollectorName = Nothing
  , G.basicBlocks = []
  }

finalizeAndReplaceWith :: BasicBlock -> CodeGen ()
finalizeAndReplaceWith b = (currentBlock <<.= b) >>= finalizeBlock

finalizeBlock :: BasicBlock -> CodeGen ()
finalizeBlock (BasicBlock n is t) = finalizedBlocks %= (BasicBlock n (reverse is) t :)

newName :: CodeGen Name
newName = UnName <$> (fresh <<+= 1)

-- ###Type conversion helpers

class (Applicative m, Monad m) => TypeConverter m where
  getFT :: TypeKey -> m FlatType
  getLLVMType :: TypeKey -> m (Maybe Type)

instance TypeConverter (StateT SuperState Identity) where
  getFT tk = use (types . at tk) >>= \case
    Nothing -> error $ "Compiler error: could not find typekey: " ++ show tk
    Just t -> return t
  getLLVMType tk = use (namedTypes . at tk)

instance TypeConverter (StateT CodeGenState (ExceptT ErrorMessage Identity)) where
  getFT tk = use (super . types . at tk) >>= \case
    Nothing -> error $ "Compiler error: could not find typekey: " ++ show tk
    Just t -> return t
  getLLVMType tk = use (super . namedTypes . at tk)

fToLLVMType :: TypeConverter m => FlatType -> m Type
fToLLVMType BoolT = return T.i1
fToLLVMType (PointerT tk) = T.ptr <$> toLLVMType False tk
fToLLVMType (StructT ps) = T.StructureType False <$> mapM (toLLVMType False . snd) ps
fToLLVMType (FuncT is o) = -- TODO: should this actually be a pointer to function?
  T.FunctionType <$> toLLVMType False o <*> mapM (toLLVMType False) is <*> return False
fToLLVMType (ProcT is os) =
  T.FunctionType T.void <$> sequence (is' ++ os') <*> return False
  where
    is' = toLLVMType False <$> is
    os' = fmap T.ptr . toLLVMType True <$> os
fToLLVMType t = return $ case t of
  FloatT{} -> T.FloatingPointType (getSize t) T.IEEE
  _ -> T.IntegerType (getSize t)

toLLVMType :: TypeConverter m => Bool -> TypeKey -> m Type
toLLVMType False tk = getLLVMType tk >>= maybe (getFT tk >>= fToLLVMType) return
toLLVMType True tk = T.ptr <$> (getLLVMType tk >>= maybe (getFT tk >>= fToLLVMType) return)

getSize :: FlatType -> Word32
getSize (IntT s) = getSizeFromTSize s
getSize (UIntT s) = getSizeFromTSize s
getSize (FloatT s) = getSizeFromTSize s
getSize BoolT = 1

-- ###Helpers:

boolean :: a -> a -> Bool -> a
boolean a b c = if c then a else b

justErr :: MonadError e m => e -> Maybe a -> m a
justErr _ (Just a) = return a
justErr err Nothing = throwError err

instance IsString Name where
  fromString = Name

-- ###Manual lenses:

blockInstrs :: Functor f => ([AST.Named AST.Instruction] -> f [AST.Named AST.Instruction]) -> AST.BasicBlock -> f AST.BasicBlock
blockInstrs inj (AST.BasicBlock n i t) = (\is -> AST.BasicBlock n is t) <$> inj i
{-# INLINE blockInstrs #-}

blockTerminator :: Functor f => (AST.Named AST.Terminator -> f (AST.Named AST.Terminator)) -> AST.BasicBlock -> f AST.BasicBlock
blockTerminator inj (AST.BasicBlock n i t) = AST.BasicBlock n i <$> inj t
{-# INLINE blockTerminator #-}

blockName :: Functor f => (AST.Name -> f AST.Name) -> AST.BasicBlock -> f AST.BasicBlock
blockName inj (AST.BasicBlock n i t) = (\n' -> AST.BasicBlock n' i t) <$> inj n
{-# INLINE blockName #-}
