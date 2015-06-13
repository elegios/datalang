{-# LANGUAGE TupleSections, FlexibleInstances #-}

module CABI.EntryPoint
( FuncSpec(..)
, DefinitionLocation(..)
, getCABI
) where

import CABI.Common
import Data.Functor ((<$>))
import Data.Maybe (fromMaybe, maybeToList)
import Data.Word (Word)
import Data.Monoid (Monoid)
import Control.Applicative ((<*))
import Control.Monad (forM)
import Control.Monad.Writer (Writer, writer, runWriter, WriterT, execWriterT)
import Control.Monad.State (StateT, modify, get, evalStateT)
import Control.Monad.Trans (lift)
import LLVM.General.AST (Name(..), Named(..), Instruction(..), Operand(..), Parameter(..), Terminator(Ret), Definition(GlobalDefinition))
import LLVM.General.AST.Type (Type(FunctionType), void, ptr)
import LLVM.General.AST.Global (BasicBlock(BasicBlock))
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

generate :: FuncSpec -> (Maybe Arg, [Arg]) -> Definition
generate f@FuncSpec{ definitionLocation = InLanguage } (mRet, is) =
  GlobalDefinition $ G.functionDefaults
  { G.name = nonMangled f
  , G.returnType = case mRet of
                    Just (Arg Direct t _ _) -> t
                    _ -> void
  , G.returnAttributes = case mRet of
                          Just (Arg Direct _ (Just a) _) -> [a]
                          _ -> []
  , G.parameters = (addRetParam parameters, False)
  , G.basicBlocks = [BasicBlock (Name "conv") instrs ret]
  }
  where
    addRetParam = case mRet of
      Just (Arg Indirect t mAttr _) -> (G.Parameter t (UnName 0) (maybeToList mAttr) :) -- TODO: is the return argument allowed to have padding before it?
      _ -> id
    run :: EntryMonad a -> (a, [Named Instruction])
    run = runWriter . flip evalStateT 1
    ((parameters, ret), instrs) = run $ do
      -- Construct the list of parameters
      (paramOps, params) <- execWriterT . forM is $ \(Arg k t a padT) -> do
        T.forM padT $ \padT' -> do
          n <- freshName
          writer ((), ([], [Parameter padT' n []]))
        n <- freshName
        let t' = if k == Indirect then ptr t else t
        writer ((), ([LocalReference t' n], [Parameter t' n $ maybeToList a]))

      -- Bitcast the parameters to conform to the inlang types
      let (args, n, r) = (argTs f, mangled f, fromMaybe void $ retty f)
          callable = ConstantOperand $ C.GlobalReference (FunctionType r args False) n
      argOps <- forM (zip3 paramOps args is) $ \(argOp, inlangT, Arg k externT _ _) -> do
        ptrOp <- case k of
          Indirect -> return argOp
          Direct -> do
            allocaOp <- instr (ptr externT) $ Alloca externT Nothing 0 []
            uinstr $ Store False allocaOp argOp Nothing 0 []
            return allocaOp
        castPtr <- instr (ptr inlangT) $ BitCast ptrOp (ptr inlangT) []
        instr inlangT (Load False castPtr Nothing 0 [])

      -- Call function, then fixup returns
      (params,) <$> case (mRet, retty f) of
        (Just (Arg Indirect externT _ _), Just inlangT) -> do
          callOp <- instr inlangT $ Call False CC.Fast [] (Right callable) ((,[]) <$> argOps) [] []
          let retPtrOp = LocalReference (ptr externT) $ UnName 0
          castPtr <- instr (ptr inlangT) $ BitCast retPtrOp (ptr inlangT) []
          uinstr $ Store False castPtr callOp Nothing 0 []
          return . Do $ Ret Nothing []
        (Just (Arg Direct externT _ _), Just inlangT) -> do
          callOp <- instr inlangT $ Call False CC.Fast [] (Right callable) ((,[]) <$> argOps) [] []
          allocaOp <- instr (ptr externT) $ Alloca externT Nothing 0 []
          castPtr <- instr (ptr inlangT) $ BitCast allocaOp (ptr inlangT) []
          uinstr $ Store False castPtr callOp Nothing 0 []
          retOp <- instr externT $ Load False allocaOp Nothing 0 []
          return . Do $ Ret (Just retOp) []
        _ -> do
          uinstr $ Call False CC.Fast [] (Right callable) ((,[]) <$> argOps) [] []
          return . Do $ Ret Nothing []

generate f@FuncSpec{ definitionLocation = External } (mRet, is) = undefined -- TODO

class Monad m => GlueGen m where
  liftGlue :: EntryMonad a -> m a
  instr :: Type -> Instruction -> m Operand
  instr t instruction = do
    n <- freshName
    liftGlue $ writer ((), [n := instruction])
    return $ LocalReference t n
  uinstr :: Instruction -> m ()
  uinstr instruction = liftGlue $ writer ((), [Do instruction])
  freshName :: m Name
  freshName = liftGlue $ (UnName <$> get) <* modify (+1)

instance GlueGen (StateT Word (Writer [Named Instruction])) where
  liftGlue = id
instance Monoid a => GlueGen (WriterT a (StateT Word (Writer [Named Instruction]))) where
  liftGlue = lift

type EntryMonad a = StateT Word (Writer [Named Instruction]) a
