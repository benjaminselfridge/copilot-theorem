{-# LANGUAGE LambdaCase, NamedFieldPuns, FlexibleInstances, RankNTypes, GADTs,
    MultiParamTypeClasses, FlexibleContexts, DataKinds #-}
{-# LANGUAGE Trustworthy #-}

module Copilot.Theorem.Prover.Z3
  ( module Data.Default
  , Options (..)
  , induction, kInduction, onlySat, onlyValidity
  )
where

import Copilot.Theorem.IL.Translate
import Copilot.Theorem.Prove (Output (..), check, Proof, Universal, Existential)
import Copilot.Theorem.IL as IL
import qualified Copilot.Theorem.Prove as P

import Control.Monad (join, msum, mzero, when, void, (>=>), liftM)
import Control.Monad.State (StateT, runStateT, get, modify)
import Control.Monad.Trans.Maybe (MaybeT (..))

import Data.Default (Default(..))
import Data.List (foldl')
import Data.Maybe (fromJust, fromMaybe)
import Data.Proxy
import Data.Word

import Data.Set (Set, (\\), union)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Language.SMTLib2 as SMT
import Language.SMTLib2.Pipe
import Language.SMTLib2.Strategy
import Language.SMTLib2.Internals.Monad
import Language.SMTLib2.Debug

import qualified Language.SMTLib2.Internals.Backend as B

import System.IO
import Control.Monad.Trans

--------------------------------------------------------------------------------

-- | Tactics

data Options = Options
  { nraNLSat :: Bool
  , startK   :: Word32
  -- The maximum number of steps of the k-induction algorithm the prover runs
  -- before giving up.
  , maxK     :: Word32

  -- If `debug` is set to `True`, the SMTLib/TPTP queries produced by the
  -- prover are displayed in the standard output.
  , debug    :: Bool
  }

instance Default Options where
  def = Options
    { nraNLSat = True
    , startK = 0
    , maxK   = 10
    , debug  = False
    }

onlySat :: Options -> Proof Existential
onlySat opts = check P.Prover
  { P.proverName  = "OnlySat"
  , P.startProver = return . ProofState opts Map.empty Map.empty Map.empty . translate
  , P.askProver   = onlySat'
  , P.closeProver = const $ return ()
  }

onlyValidity :: Options -> Proof Universal
onlyValidity opts = check P.Prover
  { P.proverName  = "OnlyValidity"
  , P.startProver = return . ProofState opts Map.empty Map.empty Map.empty . translate
  , P.askProver   = onlyValidity'
  , P.closeProver = const $ return ()
  }

induction :: Options -> Proof Universal
induction opts = check P.Prover
  { P.proverName  = "Induction"
  , P.startProver = return . ProofState opts Map.empty Map.empty Map.empty . translate
  , P.askProver   = kInduction' 0 0
  , P.closeProver = const $ return ()
  }

kInduction :: Options -> Proof Universal
kInduction opts = check P.Prover
  { P.proverName  = "K-Induction"
  , P.startProver = return . ProofState opts Map.empty Map.empty Map.empty . translate
  , P.askProver   = kInduction' (startK opts) (maxK opts)
  , P.closeProver = const $ return ()
  }

-------------------------------------------------------------------------------

-- | Checks the Copilot specification with k-induction

type Solver = DebugBackend SMTPipe

type ProofScript = MaybeT (StateT ProofState (SMT Solver))

runPS :: ProofScript a -> ProofState -> IO (Maybe a, ProofState)
runPS ps = withBackendExitCleanly (newBackend "[ignore this line]" True) . runStateT (runMaybeT ps)

data ProofState = ProofState
  { options  :: Options
  , solvers  :: Map SolverId Solver
  , vars     :: Map SolverId TransState
  , assumps  :: Map SolverId (Set IL.Expr)
  , spec     :: IL
  }

data SolverId = Base | Step
  deriving (Show, Ord, Eq)

getModels :: [PropId] -> [PropId] -> ProofScript ([IL.Expr], [IL.Expr], [IL.Expr], [IL.Expr], Bool)
getModels assumptionIds toCheckIds = do
  IL {modelInit, modelRec, properties, inductive} <- spec <$> get
  let (as, as')       = selectProps assumptionIds properties
      (as'', toCheck) = selectProps toCheckIds properties
  return (as ++ as', modelInit, modelRec ++ as ++ as' ++ as'', toCheck, inductive)

getSolver :: SolverId -> ProofScript Solver
getSolver sid = do
  solvers <- solvers <$> get
  case Map.lookup sid solvers of
    Nothing -> startNewSolver sid
    Just solver -> return solver

setSolver :: SolverId -> Solver -> ProofScript ()
setSolver sid solver =
  (lift . modify) $ \s -> s { solvers = Map.insert sid solver (solvers s) }

getVars :: SolverId -> ProofScript TransState
getVars sid = do
  vars <- vars <$> get
  return $ fromMaybe noVars (Map.lookup sid vars)

setVars :: SolverId -> TransState -> ProofScript ()
setVars sid vs =
  (lift . modify) $ \s -> s { vars = Map.insert sid vs (vars s) }

newAssumps :: SolverId -> [IL.Expr] -> ProofScript [IL.Expr]
newAssumps sid as' = do
  assumps <- assumps <$> get
  case Map.lookup sid assumps of
    Nothing -> do
      modify $ \s -> s { assumps = Map.insert sid (Set.fromList as') assumps }
      return as'
    Just as -> do
      let as'' = Set.fromList as' `union` as
      modify $ \s -> s { assumps = Map.insert sid as'' assumps }
      return $ Set.elems $ Set.fromList as' \\ as

deleteSolver :: SolverId -> ProofScript ()
deleteSolver sid =
  (lift . modify) $ \s -> s { solvers = Map.delete sid (solvers s) }

newBackend :: String -> Bool -> IO Solver
newBackend sid dbg = do
      pipe <- createPipe "z3" ["-smt2", "-in"]
      return $ debugBackend' True (not dbg) (Just sid) stdout pipe

startNewSolver :: SolverId -> ProofScript Solver
startNewSolver sid = do
  dbg <- liftM debug (options <$> get)
  b <- liftIO $ newBackend (show sid) dbg
  setSolver sid b
  return b

stop :: SolverId -> ProofScript ()
stop sid = do
  -- s <- getSolver sid
  deleteSolver sid
  -- liftIO $ close s

stopSolvers :: ProofScript ()
stopSolvers = do
  solvers <- solvers <$> get
  mapM_ stop (fst <$> Map.toList solvers)

proofKind :: Integer -> String
proofKind 0 = "induction"
proofKind k = "k-induction (k = " ++ show k ++ ")"

withSolver :: SolverId -> ProofScript ()
withSolver sid = do
      b <- getSolver sid
      doSMT $ modify $ \ss -> ss { backend = b }

doSMT :: SMT Solver a -> ProofScript a
doSMT = lift . lift

entailment :: SolverId -> [IL.Expr] -> [IL.Expr] -> ProofScript CheckSatResult
entailment sid assumptions props = do
  withSolver sid
  doSMT $ setOption (ProduceModels True)
  -- doSMT $ setOption (ProduceProofs True)
  -- doSMT $ setOption (ProduceUnsatCores True)
  vs <- getVars sid
  assumps' <- newAssumps sid assumptions
  (_, vs')  <- doSMT $ runStateT (mapM_ (transB >=> lift . assert) assumps') vs
  setVars sid vs'
  doSMT push
  _ <- doSMT $ runStateT (transB (bsimpl (foldl' (Op2 Bool IL.Or) (ConstB False) $ map (Op1 Bool IL.Not) props)) >>= lift . assert) vs'

  nraNL <- liftM nraNLSat (options <$> get)
  res <- if nraNL
    then doSMT $ checkSatWith (Just (UsingParams (CustomTactic "qfnra-nlsat") []))
         (CheckSatLimits (Just 5000) Nothing)
    else doSMT $ checkSatWith Nothing (CheckSatLimits (Just 5000) Nothing)

  when (res == Sat) $ void $ doSMT getModel
  -- when (res == Unsat) $ void $ doSMT $ getProof
  doSMT pop
  -- liftIO $ print model
  return res

unknown :: ProofScript a
unknown = mzero

unknown' :: String -> ProofScript Output
unknown' msg = return $ Output P.Unknown [msg]

invalid :: String -> ProofScript Output
invalid msg = return $ Output P.Invalid [msg]

sat :: String -> ProofScript Output
sat msg = return $ Output P.Sat [msg]

valid :: String -> ProofScript Output
valid msg = return $ Output P.Valid [msg]

kInduction' :: Word32 -> Word32 -> ProofState -> [PropId] -> [PropId] -> IO Output
kInduction' startK maxK s as ps = (fromMaybe (Output P.Unknown ["proof by " ++ proofKind (toInteger maxK) ++ " failed"]) . fst)
  <$> runPS (msum (map induction [(toInteger startK) .. (toInteger maxK)]) <* stopSolvers) s
  where
    induction k = do
      (assumps, modelInit, modelRec, toCheck, inductive) <- getModels as ps

      let base    = [evalAt (Fixed i) m | m <- modelRec, i <- [0 .. k]]
          baseInv = [evalAt (Fixed k) m | m <- toCheck]

      let step    = [evalAt (_n_plus i) m | m <- modelRec, i <- [0 .. k + 1]]
                    ++ [evalAt (_n_plus i) m | m <- toCheck, i <- [0 .. k]]
          stepInv = [evalAt (_n_plus $ k + 1) m | m <- toCheck]

      entailment Base assumps [ConstB False] >>= \case
        Unknown -> unknown
        Unsat   -> invalid "inconsistent assumptions"
        Sat     -> entailment Base (modelInit ++ base) baseInv >>= \case
          Sat     -> invalid $ "base case failed for " ++ proofKind k
          Unknown -> unknown
          Unsat   ->
            if not inductive then valid "proved without induction"
            else entailment Step step stepInv >>= \case
              Sat     -> unknown
              Unknown -> unknown
              Unsat   -> valid $ "proved with " ++ proofKind k

onlySat' :: ProofState -> [PropId] -> [PropId] -> IO Output
onlySat' s as ps = (fromJust . fst) <$> runPS (script <* stopSolvers) s
  where
    script  = do
      (assumps, modelInit, modelRec, toCheck, inductive) <- getModels as ps

      let base    = map (evalAt (Fixed 0)) modelRec
          baseInv = map (evalAt (Fixed 0)) toCheck

      entailment Base assumps [ConstB False] >>= \case
        Unknown -> unknown
        Unsat   -> invalid "inconsistent assumptions"
        Sat     -> if inductive
          then unknown' "proposition requires induction to prove."
          else entailment Base (modelInit ++ base) (map (Op1 Bool IL.Not) baseInv) >>= \case
            Unsat   -> invalid "prop not satisfiable"
            Unknown -> unknown' "failed to find a satisfying model"
            Sat     -> sat "prop is satisfiable"

onlyValidity' :: ProofState -> [PropId] -> [PropId] -> IO Output
onlyValidity' s as ps = (fromJust . fst) <$> runPS (script <* stopSolvers) s
  where
    script  = do
      (assumps, modelInit, modelRec, toCheck, inductive) <- getModels as ps

      let base    = map (evalAt (Fixed 0)) modelRec
          baseInv = map (evalAt (Fixed 0)) toCheck

      entailment Base assumps [ConstB False] >>= \case
        Unknown -> unknown
        Unsat   -> invalid "inconsistent assumptions"
        Sat     -> if inductive
          then unknown' "proposition requires induction to prove."
          else entailment Base (modelInit ++ base) baseInv >>= \case
            Unsat   -> valid "proof by Z3"
            Unknown -> unknown
            Sat     -> invalid "Z3 found a counter-example."

selectProps :: [PropId] -> Map PropId ([IL.Expr], IL.Expr) -> ([IL.Expr], [IL.Expr])
selectProps propIds properties =
  (squash . unzip) [(as, p) | (id, (as, p)) <- Map.toList properties, id `elem` propIds]
    where squash (a, b) = (concat a, b)

--------------------------------------------------------------------------------

-- | This is all very ugly. It might make better sense to go straight from Core to SMT.Expr, or maybe use SBV instead.

type Trans = StateT TransState (SMT Solver)

data TransState = TransState
  { boolVars :: Map String (B.Expr Solver 'BoolType)
  , bv8Vars  :: Map String (B.Expr Solver ('BitVecType 8))
  , bv16Vars :: Map String (B.Expr Solver ('BitVecType 16))
  , bv32Vars :: Map String (B.Expr Solver ('BitVecType 32))
  , bv64Vars :: Map String (B.Expr Solver ('BitVecType 64))
  , realVars :: Map String (B.Expr Solver 'RealType)
  }

noVars :: TransState
noVars = TransState Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty

getBoolVar :: String -> Trans (B.Expr Solver 'BoolType)
getBoolVar = getVar bool boolVars (\v s -> s {boolVars  = v})

getBV8Var  :: String -> Trans (B.Expr Solver ('BitVecType 8))
getBV8Var  = getVar (bitvec $ bw Proxy) bv8Vars  (\v s -> s {bv8Vars  = v})

getBV16Var :: String -> Trans (B.Expr Solver ('BitVecType 16))
getBV16Var = getVar (bitvec $ bw Proxy) bv16Vars (\v s -> s {bv16Vars = v})

getBV32Var :: String -> Trans (B.Expr Solver ('BitVecType 32))
getBV32Var = getVar (bitvec $ bw Proxy) bv32Vars (\v s -> s {bv32Vars = v})

getBV64Var :: String -> Trans (B.Expr Solver ('BitVecType 64))
getBV64Var = getVar (bitvec $ bw Proxy) bv64Vars (\v s -> s {bv64Vars = v})

getRealVar  :: String -> Trans (B.Expr Solver 'RealType)
getRealVar  = getVar real realVars (\v s -> s {realVars = v})

getVar t proj upd v = do
  vs <- proj <$> get
  case Map.lookup v vs of
    Nothing -> do
      newVar <- lift $ declareVarNamed t v
      modify $ upd $ Map.insert v newVar vs
      return newVar
    Just x -> return x

l3 f a b c = lift (f a b c)
l2 f a b = lift (f a b)
l1 f a = lift (f a)

transB :: IL.Expr -> Trans (B.Expr Solver 'BoolType)
transB = \case
  ConstB b           -> lift $ cbool b
  Ite _ c e1 e2      -> join $ l3 ite <$> transB c <*> transB e1 <*> transB e2
  Op1 _ IL.Not e     -> join $ l1 not' <$> transB e
  Op2 _ IL.And e1 e2 -> join $ l2 (.&.) <$> transB e1 <*> transB e2
  Op2 _ IL.Or e1 e2  -> join $ l2 (.|.) <$> transB e1 <*> transB e2
  Op2 _ IL.Eq e1 e2  -> join $ case typeOf e1 of
    Bool   -> l2 (.==.) <$> transB e1    <*> transB e2
    Real   -> l2 (.==.) <$> transR e1    <*> transR e2
    BV8    -> l2 (.==.) <$> transBV8 e1  <*> transBV8 e2
    BV16   -> l2 (.==.) <$> transBV16 e1 <*> transBV16 e2
    BV32   -> l2 (.==.) <$> transBV32 e1 <*> transBV32 e2
    -- BV64   -> l2 (.==.) <$> transBV64 e1 <*> transBV64 e2
    SBV8   -> l2 (.==.) <$> transBV8 e1  <*> transBV8 e2
    SBV16  -> l2 (.==.) <$> transBV16 e1 <*> transBV16 e2
    SBV32  -> l2 (.==.) <$> transBV32 e1 <*> transBV32 e2
    -- SBV64  -> (.==.) <$> transBV64 e1 <*> transBV64 e2
  e@(Op2 _ Le e1 e2) -> join $ case typeOf e1 of
    Bool   -> error $ "Comparing Bools: " ++ show e
    Real   -> l2 (.<=.) <$> transR e1    <*> transR e2
    BV8    -> l2 bvule  <$> transBV8 e1  <*> transBV8 e2
    BV16   -> l2 bvule  <$> transBV16 e1 <*> transBV16 e2
    BV32   -> l2 bvule  <$> transBV32 e1 <*> transBV32 e2
    -- BV64   -> l2 bvule  <$> transBV64 e1 <*> transBV64 e2
    SBV8   -> l2 bvule  <$> transBV8 e1  <*> transBV8 e2
    SBV16  -> l2 bvule  <$> transBV16 e1 <*> transBV16 e2
    SBV32  -> l2 bvule  <$> transBV32 e1 <*> transBV32 e2
    -- SBV64  -> l2 bvule  <$> transBV64 e1 <*> transBV64 e2
  e@(Op2 _ Ge e1 e2) -> join $ case typeOf e1 of
    Bool   -> error $ "Comparing Bools: " ++ show e
    Real   -> l2 (.>=.) <$> transR e1    <*> transR e2
    BV8    -> l2 bvuge  <$> transBV8 e1  <*> transBV8 e2
    BV16   -> l2 bvuge  <$> transBV16 e1 <*> transBV16 e2
    BV32   -> l2 bvuge  <$> transBV32 e1 <*> transBV32 e2
    -- BV64   -> l2 bvuge  <$> transBV64 e1 <*> transBV64 e2
    SBV8   -> l2 bvuge  <$> transBV8 e1  <*> transBV8 e2
    SBV16  -> l2 bvuge  <$> transBV16 e1 <*> transBV16 e2
    SBV32  -> l2 bvuge  <$> transBV32 e1 <*> transBV32 e2
    -- SBV64  -> l2 bvuge  <$> transBV64 e1 <*> transBV64 e2
  e@(Op2 _ Lt e1 e2) -> join $ case typeOf e1 of
    Bool   -> error $ "Comparing Bools: " ++ show e
    Real   -> l2 (.<.) <$> transR e1    <*> transR e2
    BV8    -> l2 bvult <$> transBV8 e1  <*> transBV8 e2
    BV16   -> l2 bvult <$> transBV16 e1 <*> transBV16 e2
    BV32   -> l2 bvult <$> transBV32 e1 <*> transBV32 e2
    -- BV64   -> l2 bvult <$> transBV64 e1 <*> transBV64 e2
    SBV8   -> l2 bvult <$> transBV8 e1  <*> transBV8 e2
    SBV16  -> l2 bvult <$> transBV16 e1 <*> transBV16 e2
    SBV32  -> l2 bvult <$> transBV32 e1 <*> transBV32 e2
    -- SBV64  -> l2 bvult <$> transBV64 e1 <*> transBV64 e2
  e@(Op2 _ Gt e1 e2) -> join $ case typeOf e1 of
    Bool   -> error $ "Comparing Bools: " ++ show e
    Real   -> l2 (.>.) <$> transR e1    <*> transR e2
    BV8    -> l2 bvugt <$> transBV8 e1  <*> transBV8 e2
    BV16   -> l2 bvugt <$> transBV16 e1 <*> transBV16 e2
    BV32   -> l2 bvugt <$> transBV32 e1 <*> transBV32 e2
    -- BV64   -> l2 bvugt <$> transBV64 e1 <*> transBV64 e2
    SBV8   -> l2 bvugt <$> transBV8 e1  <*> transBV8 e2
    SBV16  -> l2 bvugt <$> transBV16 e1 <*> transBV16 e2
    SBV32  -> l2 bvugt <$> transBV32 e1 <*> transBV32 e2
    -- SBV64  -> l2 bvugt <$> transBV64 e1 <*> transBV64 e2
  SVal _ s i         -> getBoolVar $ ncVar s i
  e                  -> error $ "Encountered unhandled expression (Bool): " ++ show e

ncVar :: String -> SeqIndex -> String
ncVar s (Fixed i) = s ++ "_" ++ show i
ncVar s (Var   i) = s ++ "_n" ++ show i

transR :: IL.Expr -> Trans (B.Expr Solver 'RealType)
transR = \case
  ConstR n         -> lift $ creal $ toRational n
  Ite _ c e1 e2    -> join $ l3 ite <$> transB c <*> transR e1 <*> transR e2

  Op1 _ IL.Neg e   -> join $ l1 neg <$> transR e
  Op1 _ IL.Abs e   -> join $ l1 abs' <$> transR e

  Op2 _ Add e1 e2  -> join $ l2 (.+.) <$> transR e1 <*> transR e2
  Op2 _ Sub e1 e2  -> join $ l2 (.-.) <$> transR e1 <*> transR e2
  Op2 _ Mul e1 e2  -> join $ l2 (.*.) <$> transR e1 <*> transR e2
  Op2 _ Fdiv e1 e2 -> join $ l2 (./.) <$> transR e1 <*> transR e2

  Op2 _ Pow e1 e2  -> do
      e1' <- transR e1
      e2' <- transR e2
      f <- lift $ builtIn "^" (real ::: real ::: Nil) real
      lift $ (fun f) (e1' ::: e2' ::: Nil)

  SVal _ s i       -> getRealVar $ ncVar s i
  e                -> error $ "Encountered unhandled expression (Rat): " ++ show e

-- TODO(chathhorn): bleghh
transBV8 :: IL.Expr -> Trans (B.Expr Solver ('BitVecType 8))
transBV8 = \case
  ConstI _ n      -> lift $ cbv n $ bw Proxy
  Ite _ c e1 e2   -> join $ l3 ite <$> transB c <*> transBV8 e1 <*> transBV8 e2
  -- Op1 _ IL.Abs e  -> join $ l1 abs' <$> transBV8 e
  Op1 _ IL.Neg e  -> join $ l1 bvneg <$> transBV8 e
  Op2 _ Add e1 e2 -> join $ l2 bvadd <$> transBV8 e1 <*> transBV8 e2
  Op2 _ Sub e1 e2 -> join $ l2 bvsub <$> transBV8 e1 <*> transBV8 e2
  Op2 _ Mul e1 e2 -> join $ l2 bvmul <$> transBV8 e1 <*> transBV8 e2
  SVal _ s i      -> getBV8Var $ ncVar s i
  e               -> error $ "Encountered unhandled expression (BV8): " ++ show e

transBV16 :: IL.Expr -> Trans (B.Expr Solver ('BitVecType 16))
transBV16 = \case
  ConstI _ n      -> lift $ cbv n $ bw Proxy
  Ite _ c e1 e2   -> join $ l3 ite <$> transB c <*> transBV16 e1 <*> transBV16 e2
  -- Op1 _ IL.Abs e  -> join $ l1 abs' <$> transBV16 e
  Op1 _ IL.Neg e  -> join $ l1 bvneg <$> transBV16 e
  Op2 _ Add e1 e2 -> join $ l2 bvadd <$> transBV16 e1 <*> transBV16 e2
  Op2 _ Sub e1 e2 -> join $ l2 bvsub <$> transBV16 e1 <*> transBV16 e2
  Op2 _ Mul e1 e2 -> join $ l2 bvmul <$> transBV16 e1 <*> transBV16 e2
  SVal _ s i      -> getBV16Var $ ncVar s i
  e               -> error $ "Encountered unhandled expression (BV16): " ++ show e

transBV32 :: IL.Expr -> Trans (B.Expr Solver ('BitVecType 32))
transBV32 = \case
  ConstI _ n      -> lift $ cbv n $ bw Proxy
  Ite _ c e1 e2   -> join $ l3 ite <$> transB c <*> transBV32 e1 <*> transBV32 e2
  -- Op1 _ IL.Abs e  -> join $ l1 abs' <$> transBV32 e
  Op1 _ IL.Neg e  -> join $ l1 bvneg <$> transBV32 e
  Op2 _ Add e1 e2 -> join $ l2 bvadd <$> transBV32 e1 <*> transBV32 e2
  Op2 _ Sub e1 e2 -> join $ l2 bvsub <$> transBV32 e1 <*> transBV32 e2
  Op2 _ Mul e1 e2 -> join $ l2 bvmul <$> transBV32 e1 <*> transBV32 e2
  SVal _ s i      -> getBV32Var $ ncVar s i
  e               -> error $ "Encountered unhandled expression (BV32): " ++ show e

transBV64 :: IL.Expr -> Trans (B.Expr Solver ('BitVecType 64))
transBV64 = \case
  ConstI _ n      -> lift $ cbv n $ bw Proxy
  Ite _ c e1 e2   -> join $ l3 ite <$> transB c <*> transBV64 e1 <*> transBV64 e2
  -- Op1 _ IL.Abs e  -> join $ l1 abs' <$> transBV64 e
  Op1 _ IL.Neg e  -> join $ l1 bvneg <$> transBV64 e
  Op2 _ Add e1 e2 -> join $ l2 bvadd <$> transBV64 e1 <*> transBV64 e2
  Op2 _ Sub e1 e2 -> join $ l2 bvsub <$> transBV64 e1 <*> transBV64 e2
  Op2 _ Mul e1 e2 -> join $ l2 bvmul <$> transBV64 e1 <*> transBV64 e2
  SVal _ s i      -> getBV64Var $ ncVar s i
  e               -> error $ "Encountered unhandled expression (BV64): " ++ show e

