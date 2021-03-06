{-# LANGUAGE TemplateHaskell, TupleSections, LambdaCase, FlexibleInstances #-}

module NameResolution (resolveNames) where

import GlobalAst (SourceRange(..), location)
import Parser.Ast
import NameResolution.Ast
import Data.Functor ((<$>))
import Data.List ((\\))
import Data.Generics.Uniplate.Direct (universe)
import Control.Lens hiding (both, universe)
import Control.Applicative (Applicative, (<*>))
import Control.Monad (zipWithM_)
import Control.Monad.State (evalStateT, StateT, get, put)
import Control.Monad.Except (runExceptT, ExceptT, MonadError, throwError)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Traversable as T

data ResolverState = ResolverState
  { _scope :: M.Map String Resolved
  }

data ErrorMessage = ErrorString String deriving Show

type Resolver a = StateT ResolverState (ExceptT ErrorMessage Identity) a

makeLenses ''ResolverState

resolveNames :: SourceFileT String -> Either [ErrorMessage] ResolvedSource
resolveNames (SourceFile tDefs cDefs cImps cExps) = eResolvedFile
  where
    eResolvedFile = fmap ResolvedSource tMap `mergeApply` cMap `mergeApply` eCImps `mergeApply` eCExps
    (tMap, cMap) = (mapWith typeName <$> eTypes, mapWith callableName <$> eCallables)
    eCallables = foldEithers $ run . resolve <$> cDefs
    eCImps = foldEithers $ run . resolve <$> cImps
    eCExps = foldEithers $ run . resolve <$> cExps
    eTypes = case checkTypeDefs tDefs of
      [] -> foldEithers $ map (run . resolveTypeDef (mapWith typeName tDefs)) tDefs
      es -> Left es
    names = (callableName <$> cDefs) ++ (inLangName <$> cImps)
    inLangName (Request n _ _) = n
    initState = ResolverState $ M.fromList . zip names $ Global <$> names
    mergeApply (Left e1) (Left e2) = Left $ e1 ++ e2
    mergeApply (Left e) _ = Left e
    mergeApply _ (Left e) = Left e
    mergeApply (Right f) (Right a) = Right $ f a
    run m = runIdentity . runExceptT $ evalStateT m initState

foldEithers :: [Either a b] -> Either [a] [b]
foldEithers = foldl foldF $ Right []
  where
    foldF (Left es) (Left e) = Left $ e : es
    foldF l@Left{} _ = l
    foldF _ (Left e) = Left [e]
    foldF (Right as) (Right a) = Right $ a : as

mapWith :: Ord k => (a -> k) -> [a] -> M.Map k a
mapWith f es = M.fromList $ zip (map f es) es

define :: SourceRange -> String -> Resolved -> Resolver ()
define sr n r@(Local _) =
  (scope . at n <<.= Just r) >>= \case
    Just (Local _) -> throwError . ErrorString $ "Redefinition of " ++ n ++ " at " ++ show sr
    _ -> return ()

instance Resolvable (RequestT Type) where
  resolve (Request n n' t) = return $ Request (Global n) n' t -- TODO: different with modules/namespaces

instance Resolvable CallableDefT where
  resolve d@FuncDef{ inargs = is
                   , outarg = o
                   , callableBody = b } = do
    let is' = Local <$> is
        o' = Local o
    prevScope <- use scope
    zipWithM_ (define $ location d) is is'
    define (location d) o o'
    b' <- resolve b
    scope .= prevScope
    return $ d {callableBody = b', inargs = is', outarg = o'}
  resolve d@ProcDef{ inargs = is
                   , outargs = os
                   , callableBody = b } = do
    let is' = Local <$> is
        os' = Local <$> os
    prevScope <- use scope
    zipWithM_ (define $ location d) is is'
    zipWithM_ (define $ location d) os os'
    b' <- resolve b
    scope .= prevScope
    return $ d {callableBody = b', inargs = is', outargs = os'}

instance Resolvable StatementT where
  resolve (Defer s r) = Defer <$> resolve s <*> return r
  resolve (ShallowCopy e1 e2 r) = ShallowCopy <$> resolve e1 <*> resolve e2 <*> return r
  resolve (While c s r) = While <$> resolve c <*> resolve s <*> return r
  resolve (Terminator t r) = return $ Terminator t r
  resolve (If c ts mes r) =
    If <$> resolve c <*> resolve ts <*> T.mapM resolve mes <*> return r
  resolve (ProcCall inl c i o r) =
    ProcCall inl <$> resolve c <*> mapM resolve i <*> mapM eitherResolve o <*> return r
    where
      eitherResolve (Left a) = Left <$> resolve a
      eitherResolve (Right a) = Right <$> resolve a
  resolve (Scope s r) = do
    prevState <- get
    s' <- mapM resolve s
    put prevState
    return $ Scope s' r
  resolve (VarInit mut n mt me r) = do
    me' <- T.mapM resolve me
    let n' = Local n
    define r n n'
    return $ VarInit mut n' mt me' r

instance Resolvable ExpressionT where
  resolve (Bin o e1 e2 r) = Bin o <$> resolve e1 <*> resolve e2 <*> return r
  resolve (Un o e r) = Un o <$> resolve e <*> return r
  resolve (FuncCall inl c i r) =
    FuncCall inl <$> resolve c <*> mapM resolve i <*> return r
  resolve (ExprLit l) = ExprLit <$> resolve l
  resolve (TypeAssertion e t r) = TypeAssertion <$> resolve e <*> return t <*> return r
  resolve (MemberAccess e m r) =
    MemberAccess <$> resolve e <*> return m <*> return r -- TODO: more fancy when modules are a thing
  resolve (Subscript e bs r) =
    Subscript <$> resolve e <*> mapM (T.mapM resolve) bs <*> return r
  resolve (NewTypeConversion e n r) =
    NewTypeConversion <$> resolve e <*> return n <*> return r
  resolve (Variable n r) =
    Variable <$> (use (scope . at n) >>= justErr err) <*> return r
    where err = ErrorString $ "Unknown variable " ++ n ++ " at " ++ show r

instance Resolvable LiteralT where
  resolve (ILit i r) = return $ ILit i r
  resolve (FLit f r) = return $ FLit f r
  resolve (BLit b r) = return $ BLit b r
  resolve (Null r) = return $ Null r
  resolve (Undef r) = return $ Undef r
  resolve (StructLit ps r) = flip StructLit r <$> mapM (rightA resolve) ps
  resolve (StructTupleLit ps r) = flip StructTupleLit r <$> mapM resolve ps

class Resolvable r where
  resolve :: r String -> Resolver (r Resolved)

-- Type resolving

resolveTypeDef :: M.Map String (TypeDefT String) -> TypeDefT String -> Resolver (TypeDefT Resolved)
resolveTypeDef _ (Alias tn tp w r) = return $ Alias tn tp w r
resolveTypeDef tMap (NewType tn tp hi ai bp w r) = do
  ids <- M.fromList . map (\n -> (n, ReplacementLocal True n)) <$> getIdentifiers tMap w
  scope %= M.union (M.insert "self" Self ids)
  ai' <- mapM resolveIdentifiers ai
  bp' <- mapM resolveBrackets bp
  return $ NewType tn tp hi ai' bp' w r
  where
    resolveReplacement (me, e) = (,) <$> T.mapM resolve me <*> resolve e
    resolveIdentifiers (i, rep) = (i,) <$> resolveReplacement rep
    resolveBr (BrId n me) = BrId (ReplacementLocal False n) <$> T.mapM resolve me
    resolveBr (BrOp n) = return $ BrOp n
    resolveBrackets (p, rep) = do
      p' <- mapM resolveBr p
      prevScope <- scope <<%= M.union newIds
      rep' <- resolveReplacement rep
      scope .= prevScope
      return (p', rep')
      where newIds = M.fromList [(n, ReplacementLocal False n) | BrId n _ <- p]

getIdentifiers :: M.Map String (TypeDefT String) -> Type -> Resolver [String]
getIdentifiers _ (StructT props _) = return $ fst <$> props
getIdentifiers tMap (PointerT t _) = getIdentifiers tMap t
getIdentifiers tMap (NamedT tName _ range) = tLookup >>= \td -> case td of
  Alias{wrappedType = t} -> getIdentifiers tMap t
  NewType { hiddenIdentifiers = hi
          , introducedIdentifiers = ai
          , wrappedType = t
          } -> (map fst ai ++) . hide hi <$> getIdentifiers tMap t
  where
    tLookup = justErr (ErrorString $ "Unknown type " ++ tName ++ " at " ++ show range) $
              M.lookup tName tMap
    hide HideAll _ = []
    hide (HideSome h) o = o \\ h
getIdentifiers _ _ = return []

checkTypeDefs :: [TypeDefT String] -> [ErrorMessage]
checkTypeDefs tds = dupErrs ++ recurse (typeGraph tds)
  where
    recurse [] = []
    recurse g
      | g /= g' = recurse g'
      | otherwise = map cycleErr . S.toList $ S.intersection keys elems
      where
        g' = filter ((`S.member` keys) . snd) g
        keys = S.fromList $ fst <$> g
        elems = S.fromList $ snd <$> g
        cycleErr (n, r) = ErrorString $ n ++ " at " ++ show r ++ " is part of a bad type cycle"
    (dupErrs, _) = foldl checkDups ([], S.empty) tds
    checkDups (es, ds) d
      | typeName d `S.member` ds = (err : es, ds)
      | otherwise = (es, typeName d `S.insert` ds)
      where
        err = ErrorString $ "Redefinition of " ++ typeName d ++ " at " ++ show (location d)

-- BUG: should check for cycles separately between aliases and newtypes
{-
an alias should depend on all mentioned aliases
a newtype should depend on newtypes in a top-level struct, the type under a chain of top-level pointers, the top-level type and all newtypes occurring as type parameters to newtypes in those positions
I at least think that is correct
Examples:

alias A B // deps []
type B A  // deps [B]

alias Pair<a,b> { first : a, second : b } // deps []
type LL<a> Pair<a,^LL<a>>                 // deps []

alias Pair<a,b> { first : a, second : ^b } // deps []
type LL<a> Pair<a,LL<a>>                   // deps []

alias A {a : Bool, b : B} // deps []
type B ^A                 // deps []
-}
typeGraph :: [TypeDefT String] -> [((String, SourceRange), (String, SourceRange))]
typeGraph defs = defs >>= \d -> zip (repeat (typeName d, location d)) $ deps d
  where
    deps Alias{wrappedType = w} = [ (n, r) | NamedT n _ r <- universe w ]
    deps NewType{wrappedType = w} = newDeps w
    newDeps (PointerT t _) = newDeps t
    newDeps t = innerDeps t
    innerDeps (NamedT tName ts r) = (tName, r) : concatMap newDeps ts -- BUG: might be too strong, not sure what to do instead though
    innerDeps (StructT ps _) = concatMap innerDeps $ snd <$> ps
    innerDeps _ = []

-- Somewhat general functions

justErr :: MonadError e m => e -> Maybe a -> m a
justErr _ (Just a) = return a
justErr err Nothing = throwError err

rightA :: Applicative f => (b -> f c) -> (a, b) -> f (a, c)
rightA f (a, b) = (a,) <$> f b
