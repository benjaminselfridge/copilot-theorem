--------------------------------------------------------------------------------

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Trustworthy #-}

module Copilot.Theorem.Kind2.Prover
  ( module Data.Default
  , Options (..)
  , kind2Prover
  ) where

import Copilot.Theorem.Prove
import Copilot.Theorem.Kind2.Output
import Copilot.Theorem.Kind2.PrettyPrint
import Copilot.Theorem.Kind2.Translate

-- It seems [IO.openTempFile] doesn't work on Mac OSX
import System.IO hiding (openTempFile)
import Copilot.Theorem.Misc.Utils (openTempFile)

import System.Process

import System.Directory
import Data.Default

import qualified Copilot.Theorem.TransSys as TS

--------------------------------------------------------------------------------

data Options = Options
  { bmcMax :: Int }

instance Default Options where
  def = Options { bmcMax = 0 }

data ProverST = ProverST
  { options  :: Options
  , transSys :: TS.TransSys }

kind2Prover :: Options -> Prover
kind2Prover opts = Prover
  { proverName =  "Kind2"
  , startProver  = return . ProverST opts . TS.translate
  , askProver    = askKind2
  , closeProver  = const $ return () }

--------------------------------------------------------------------------------

kind2Prog        = "kind2"
kind2BaseOptions = ["--input-format", "native", "-xml"]

--------------------------------------------------------------------------------

askKind2 :: ProverST -> [PropId] -> [PropId] -> IO Output
askKind2 (ProverST opts spec) assumptions toCheck = do

  let kind2Input = prettyPrint . toKind2 Inlined assumptions toCheck $ spec

  (tempName, tempHandle) <- openTempFile "." "out" "kind"
  hPutStr tempHandle kind2Input
  hClose tempHandle

  let kind2Options =
        kind2BaseOptions ++ ["--bmc_max", show $ bmcMax opts, tempName]

  (_, output, _) <- readProcessWithExitCode kind2Prog kind2Options ""

  putStrLn kind2Input

  removeFile tempName
  return $ parseOutput (head toCheck) output -- TODO support multiple toCheck props

--------------------------------------------------------------------------------
