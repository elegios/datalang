module CABI.X86_64 (convertFunc) where

import CABI.Common (Arg(Arg), ArgType(..))
import Control.Monad (forM_)
import Control.Monad.Writer (WriterT, writer, execWriterT)
import Control.Monad.State (StateT, modify, get, evalStateT)
import Control.Monad.Trans (lift)
import Data.Word (Word32)
import Data.List (groupBy)
import Data.Function (on)
import Data.Functor ((<$>))
import Data.Maybe (fromJust)
import Data.Generics.Uniplate.Direct (transform)
import LLVM.General.AST.Type
import LLVM.General.AST (Name)
import LLVM.General.AST.Attribute (ParameterAttribute(SRet, ByVal))
import qualified Data.Map as M

type FlattenMonad a = StateT Word32 (WriterT [(Word32, Type)] Maybe) a

convertFunc :: M.Map Name Type -> Maybe Type -> [Type] -> (Maybe Arg, [Arg])
convertFunc nts mRetty inTys =
  (convertType nts SRet <$> mRetty, convertType nts ByVal <$> inTys)

convertType :: M.Map Name Type -> ParameterAttribute -> Type -> Arg
convertType nts attr t
  | numWords > 4 = Arg Indirect t (Just attr) Nothing
  | numWords > 2 = case t of
    VectorType{} -> Arg Direct t Nothing Nothing
    _ -> Arg Indirect t (Just attr) Nothing
  | otherwise = case run . alignedFlatten $ unnamedT of
    Nothing -> Arg Indirect t (Just attr) Nothing
    Just llvmts -> case findWordType <$> groupWords llvmts of
      [v@VectorType{}] -> Arg Direct v Nothing Nothing
  where
    numWords = (typeSize t + wordSize - 1) `div` wordSize
    unnamedT = removeNames nts t
    run = execWriterT . flip evalStateT 0
    groupWords = map (map snd) . groupBy ((==) `on` (`div` wordSize) . fst)
    findWordType [f@(FloatingPointType 32 _), FloatingPointType 32 _] =
      VectorType 2 f
    findWordType ts
      | any isInt ts = IntegerType 64
    findWordType [it] = it -- NOTE: Vectors are passed as is
    findWordType ts = error $ "Unexpected types in findWordType: " ++ show ts
    isInt IntegerType{} = True
    isInt PointerType{} = True
    isInt _ = False

typeAlign :: Type -> Word32
typeAlign (IntegerType s) = (s + 7) `div` 8
typeAlign PointerType{} = 8
typeAlign (FloatingPointType s _) = s `div` 8
typeAlign (StructureType True _) = 1
typeAlign (StructureType False ts) = maximum $ typeAlign <$> ts
typeAlign (ArrayType _ t) = typeAlign t
typeAlign (VectorType len t) = len * typeAlign t

typeSize :: Type -> Word32
typeSize (IntegerType s) = (s + 7) `div` 8
typeSize PointerType{} = 8
typeSize (FloatingPointType s _) = s `div` 8
typeSize (StructureType True ts) = sum $ typeSize <$> ts
typeSize (StructureType False ts) = foldl (\s t -> align t s + typeSize t) 0 ts
typeSize (ArrayType len t) = fromIntegral len * typeSize t
typeSize (VectorType len t) = len * typeSize t

wordSize :: Word32
wordSize = 8

alignedFlatten :: Type -> FlattenMonad ()
alignedFlatten (StructureType packed ts)
  | packed = mapM_ alignedFlatten ts
  | otherwise = forM_ ts $ \t -> modify (align t) >> alignedFlatten t
alignedFlatten (ArrayType num t) = massSave (fromIntegral num) t
alignedFlatten t = save t -- NOTE: flat types, these are merely saved to the list

save :: Type -> FlattenMonad ()
save t = do
  start <- get
  if isAligned t start
    then writer ((), [(start, t)]) >> modify (+ typeSize t)
    else lift . lift $ Nothing

massSave :: Int -> Type -> FlattenMonad ()
massSave num t = do
  start <- get
  if isAligned t start
    then writer ((), zip [start, start + typeSize t ..] $ replicate num t)
    else lift . lift $ Nothing

align :: Type -> Word32 -> Word32
align t v = ((v + a - 1) `div` a) * a
  where a = typeAlign t

isAligned :: Type -> Word32 -> Bool
isAligned t v = (v `mod` typeAlign t) == 0

removeNames :: M.Map Name Type -> Type -> Type
removeNames tns = transform inner
  where inner (NamedTypeReference n) = transform inner . fromJust $ M.lookup n tns
        inner x = x
