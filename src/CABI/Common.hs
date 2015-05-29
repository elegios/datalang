module CABI.Common where

import Data.Generics.Uniplate.Direct
import LLVM.General.AST.Type
import LLVM.General.AST.Attribute (ParameterAttribute)

{-
NOTE: this instance is actually incorrect compared to what one would
normally want in a uniplate instance. Instead of getting all types it
only gets types that are not pointed at by a pointer. Might be worth
putting it into a newtype to make it a bit more clear.
-}
instance Uniplate Type where
  uniplate (IntegerType s) = plate IntegerType |- s
  uniplate (PointerType a t) = plate PointerType |- a |- t
  uniplate (FloatingPointType s ieee) = plate FloatingPointType |- s |- ieee
  uniplate (StructureType p ts) = plate StructureType |- p ||* ts
  uniplate (ArrayType len t) = plate ArrayType |- len |* t
  uniplate (VectorType len t) = plate VectorType |- len |* t
  uniplate (NamedTypeReference n) = plate NamedTypeReference |- n
  uniplate t = error $ "Did not expect " ++ show t ++ " in the uniplate instance for AST.Type"

data Arg = Arg { kind :: ArgType, llvmType :: Type, attr :: Maybe ParameterAttribute, padding :: Maybe Type }
data ArgType = Direct | Indirect deriving Eq
