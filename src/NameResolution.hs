{-# LANGUAGE TemplateHaskell, TupleSections, LambdaCase #-}

module NameResolution
( resolveNames
, Resolved(..)
, ResolvedSource(..)
, ErrorMessage(..)
) where

import Ast (SourceRange(..), location)
import Parser hiding (parseFile)
import Data.Functor ((<$>))
import Data.List ((\\))
import Control.Lens hiding (both)
import Control.Applicative ((<*>))
import Control.Monad (zipWithM_)
import Control.Monad.State (evalStateT, StateT, get, put)
import Control.Monad.Except (runExceptT, ExceptT, MonadError, throwError)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Traversable as T

data Resolved = Local
                { depth :: Int
                , name :: String
                }
              | Global
                { name :: String
                }
              | ReplacementLocal
                { member :: Bool
                , name :: String
                }
              | Self
              deriving (Eq, Ord, Show)

data ResolvedSource = ResolvedSource
  { types :: M.Map String (TypeDefT Resolved)
  , callables :: M.Map String (CallableDefT Resolved)
  }

data ResolverState = ResolverState
  { _currentDepth :: Int
  , _scope :: M.Map String Resolved
  }

data ErrorMessage = ErrorString String | AlreadyReportedError deriving Show

type Resolver a = StateT ResolverState (ExceptT ErrorMessage Identity) a

makeLenses ''ResolverState

resolveNames :: SourceFileT String -> Either [ErrorMessage] ResolvedSource
resolveNames (SourceFile tDefs cDefs) = eResolvedFile
  where
    eResolvedFile = fmap ResolvedSource tMap `mergeApply` cMap
    (tMap, cMap) = (mapWith typeName <$> eTypes, mapWith callableName <$> eCallables)
    eCallables = foldEithers $ run . resolve <$> cDefs
    eTypes = case checkTypeDefs tDefs of
      [] -> foldEithers $ map (run . resolveTypeDef (mapWith typeName tDefs)) tDefs
      es -> Left es
    names = callableName <$> cDefs
    initState = ResolverState 0 $ M.fromList . zip names $ Global <$> names
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
define sr n r@(Local d _) =
  (scope . at n <<.= Just r) >>= \case
    Just (Local d' _) | d == d' -> throwError . ErrorString $ "Redefinition of " ++ n ++ " at " ++ show sr
    _ -> return ()

instance Resolvable CallableDefT where
  resolve d@FuncDef{ inargs = is
                   , outarg = o
                   , callableBody = b } = do
    let is' = Local 0 <$> is
        o' = Local 0 o
    prevScope <- use scope
    zipWithM_ (define $ location d) is is'
    define (location d) o o'
    b' <- resolve b
    scope .= prevScope
    return $ d {callableBody = b', inargs = is', outarg = o'}
  resolve d@ProcDef{ inargs = is
                   , outargs = os
                   , callableBody = b } = do
    let is' = Local 0 <$> is
        os' = Local 0 <$> os
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
  resolve (ProcCall c i o r) =
    ProcCall <$> resolve c <*> mapM resolve i <*> mapM resolve o <*> return r
  resolve (Scope s r) = do
    prevState <- get
    currentDepth += 1
    s' <- mapM resolve s
    put prevState
    return $ Scope s' r
  resolve (VarInit mut n mt me r) = do
    me' <- T.mapM resolve me
    d <- use currentDepth
    let n' = Local d n
    define r n n'
    return $ VarInit mut n' mt me' r

instance Resolvable ExpressionT where
  resolve (Bin o e1 e2 r) = Bin o <$> resolve e1 <*> resolve e2 <*> return r
  resolve (Un o e r) = Un o <$> resolve e <*> return r
  resolve (FuncCall c i r) = FuncCall <$> resolve c <*> mapM resolve i <*> return r
  resolve (ExprLit l) = return $ ExprLit l
  resolve (TypeAssertion e t r) = TypeAssertion <$> resolve e <*> return t <*> return r
  resolve (MemberAccess e m r) =
    MemberAccess <$> resolve e <*> return m <*> return r -- TODO: more fancy when modules are a thing
  resolve (Subscript e bs r) =
    Subscript <$> resolve e <*> mapM (T.mapM resolve) bs <*> return r
  resolve (Variable n r) =
    Variable <$> (use (scope . at n) >>= justErr err) <*> return r
    where err = ErrorString $ "Unknown variable " ++ n ++ " at " ++ show r

class Resolvable r where
  resolve :: r String -> Resolver (r Resolved)

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

typeGraph :: [TypeDefT String] -> [((String, SourceRange), (String, SourceRange))]
typeGraph defs = defs >>= \d -> zip (repeat (typeName d, location d)) $ deps (wrappedType d)
  where
    deps (PointerT t _) = deps t
    deps t = innerDeps t
    innerDeps (NamedT tName ts r) = (tName, r) : concatMap deps ts -- BUG: might be too strong, not sure what to do instead though
    innerDeps (StructT ps _) = concatMap innerDeps $ snd <$> ps
    innerDeps _ = []

justErr :: MonadError e m => e -> Maybe a -> m a
justErr _ (Just a) = return a
justErr err Nothing = throwError err
