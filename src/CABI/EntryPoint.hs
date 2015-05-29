{-# LANGUAGE TupleSections #-}

module CABI.EntryPoint
( FuncSpec(..)
, DefinitionLocation(..)
, getCABI
) where

import CABI.Common
import Data.Functor ((<$>))
import Data.Maybe (fromMaybe, maybeToList)
import Data.Word (Word)
import Control.Applicative ((<*))
import Control.Monad.Writer (Writer, writer, runWriter)
import Control.Monad.State (StateT, modify, get, execStateT, evalStateT)
import LLVM.General.AST (Name(..), Named(..), Instruction(..))
import LLVM.General.AST.Type (Type, void, ptr)
import qualified CABI.X86_64 as X86_64
import qualified Data.Map as M
import qualified Data.Traversable as T
import qualified LLVM.General.AST as AST
import qualified LLVM.General.AST.Global as G
import qualified LLVM.General.AST.Constant as C
import qualified LLVM.General.AST.CallingConvention as CC

data FuncSpec = FuncSpec
                { retty :: Maybe Type
                , argTs :: [Type]
                , nonMangled :: Name
                , mangled :: Name
                , definitionLocation :: DefinitionLocation
                }
data DefinitionLocation = InLanguage | External

getCABI :: String -> M.Map Name Type -> FuncSpec -> AST.Definition
getCABI triple nts spec =
  generate spec $
  call spec $
  case takeWhile ('-' /=) triple of
    "x86_64" -> X86_64.convertFunc
    arch -> error $ "Unknown/unsupported arch: " ++ show arch
  where
    call s f = f nts (retty s) (argTs s)

generate :: FuncSpec -> (Maybe Arg, [Arg]) -> AST.Definition
generate f@FuncSpec{ definitionLocation = InLanguage } (mRet, is) =
  AST.GlobalDefinition $ G.functionDefaults
  { G.name = nonMangled f
  , G.returnType = case mRet of
                    Just (Arg Direct t _ _) -> t
                    _ -> void
  , G.returnAttributes = case mRet of
                          Just (Arg Direct _ (Just a) _) -> [a]
                          _ -> []
  , G.parameters = (addRetParam params, False)
  , G.basicBlocks = [AST.BasicBlock (Name "conv") (callPrepInstrs ++ [call] ++ afterCallInstrs) ret]
  }
  where
    addRetParam = case mRet of
      Just (Arg Indirect t mAttr _) -> (G.Parameter t (UnName 0) (maybeToList mAttr) :) -- TODO: is the return argument allowed to have padding before it?
      _ -> id
    (nAfterParams, (paramOps, params)) = run 1 $ mapM_ paramF is
    paramF :: Arg -> GenMon AST.Operand G.Parameter ()
    paramF (Arg k t a padT) = do
      T.forM padT $ \padT' -> do
        n <- freshName
        writeB $ G.Parameter padT' n []
      n <- freshName
      let t' = if k == Indirect then ptr t else t
      writeB . G.Parameter t' n $ maybeToList a
      writeA $ AST.LocalReference t' n
    run firstN = runWriter . flip execStateT firstN
    freshName :: GenMon a b Name
    freshName = (UnName <$> get) <* modify (+1)
    writeA :: a -> GenMon a b ()
    writeA a = writer ((), ([a], []))
    writeB :: b -> GenMon a b ()
    writeB b = writer ((), ([], [b]))
    instr :: Type -> Instruction -> GenMon a (Named Instruction) AST.Operand
    instr t instruction = do
      n <- freshName
      writeB $ n := instruction
      return $ AST.LocalReference t n
    uinstr instruction = writeB $ Do instruction
    (nAfterCallPrep, (callParamOps, callPrepInstrs)) =
      run nAfterParams . mapM_ gen $ zip3 paramOps (argTs f) is
    call = (case mRet of
      Nothing -> Do
      Just _ -> (UnName nAfterCallPrep :=)) $
           Call False CC.Fast [] (Right callable) ((,[]) <$> callParamOps) [] []
      where
        (args, n) = (argTs f, mangled f)
        callable = AST.ConstantOperand $
                   C.GlobalReference (AST.FunctionType r args False) n
        r = fromMaybe void $ retty f
    gen :: (AST.Operand, Type, Arg) -> GenMon AST.Operand (Named Instruction) ()
    gen (argOp, inlangT, Arg k externT _ _) = do
      ptrOp <- case k of
        Indirect -> return argOp
        Direct -> do
          allocaOp <- instr (ptr externT) $ Alloca externT Nothing 0 []
          uinstr $ Store False allocaOp argOp Nothing 0 []
          return allocaOp
      castPtr <- instr (ptr inlangT) $ BitCast ptrOp (ptr inlangT) []
      instr inlangT (Load False castPtr Nothing 0 []) >>= writeA
    (ret, (_, afterCallInstrs)) = runWriter . flip evalStateT (nAfterCallPrep + 1) $
      case (mRet, retty f) of
        (Just (Arg Indirect externT _ _), Just inlangT) -> do
          let retPtrOp = AST.LocalReference (ptr externT) $ UnName 0
          castPtr <- instr (ptr inlangT) $ BitCast retPtrOp (ptr inlangT) []
          uinstr $ Store False castPtr (AST.LocalReference inlangT $ UnName nAfterCallPrep) Nothing 0 []
          return . Do $ AST.Ret (Just retPtrOp) []
        (Just (Arg Direct externT _ _), Just inlangT) -> do
          allocaOp <- instr (ptr externT) $ Alloca externT Nothing 0 []
          castPtr <- instr (ptr inlangT) $ BitCast allocaOp (ptr inlangT) []
          uinstr $ Store False castPtr (AST.LocalReference inlangT $ UnName nAfterCallPrep) Nothing 0 []
          retOp <- instr externT $ Load False allocaOp Nothing 0 []
          return . Do $ AST.Ret (Just retOp) []
        _ -> return . Do $ AST.Ret Nothing []

type GenMon a b i = StateT Word (Writer ([a], [b])) i
