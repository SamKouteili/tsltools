-- | Utilities related to LTL synthesis.
module TSL.LTL (synthesize, synthesize', realizable) where

import Control.Exception (handle)
import Control.Monad (unless)
import Data.Maybe (isJust)
import qualified Syfco as S
import System.Directory (findExecutable)
import System.Exit (ExitCode (ExitSuccess))
import System.Process (readProcessWithExitCode)
import TSL.Error (genericError, unwrap)

-- | Given LTL spec in TLSF format, synthesize a Right HOA controller
--   If unrealizable, generate a Left counterstrategy
synthesize :: FilePath -> Bool -> String -> IO (Maybe String)
synthesize ltlsyntPath finiteMode tlsfContents = do
  (exitCode, stdout, stderr) <- synthesize' ltlsyntPath finiteMode tlsfContents
  if exitCode /= ExitSuccess
    then return Nothing
    else return . Just . unlines . tail . lines $ stdout

realizable :: FilePath -> Bool -> String -> IO Bool
realizable ltlsyntPath finiteMode tlsfContents = do
  (exitCode, _, _) <- synthesize' ltlsyntPath finiteMode tlsfContents
  if exitCode /= ExitSuccess
    then return True
    else return False

synthesize' :: FilePath -> Bool -> String -> IO (ExitCode, String, String)
synthesize' ltlsyntPath finiteMode tlsfContents = do
  let synthTool = if finiteMode then "ltlfsynt" else ltlsyntPath
  -- check if synth tool is available on path
  synthToolAvailable <- checkLtlsynt synthTool
  unless synthToolAvailable $
    unwrap . genericError $
      "Invalid path to synthesis tool: " ++ synthTool

  -- prepare arguments for ltlsynt
  let tlsfSpec =
        case S.fromTLSF tlsfContents of
          Left err -> error $ show err
          Right spec -> spec
  let ltlIns = prInputs S.defaultCfg tlsfSpec
      ltlOuts = prOutputs S.defaultCfg tlsfSpec
      ltlFormulae = prFormulae S.defaultCfg {S.outputMode = S.Fully, S.outputFormat = S.LTLXBA} tlsfSpec
      ltlCommandArgs =
        [ "--formula=" ++ ltlFormulae,
          "--ins=" ++ ltlIns,
          "--outs=" ++ ltlOuts,
          "--hoaf=i"
        ]

  -- call synthesis tool
  readProcessWithExitCode synthTool ltlCommandArgs ""
  where
    prFormulae ::
      S.Configuration -> S.Specification -> String
    prFormulae c s = case S.apply c s of
      Left err -> show err
      Right formulae -> formulae

    -- \| Prints the input signals of the given specification.
    prInputs ::
      S.Configuration -> S.Specification -> String
    prInputs c s = case S.inputs c s of
      Left err -> show err
      Right [] -> ""
      Right (x : xr) -> x ++ concatMap ((:) ',' . (:) ' ') xr

    -- \| Prints the output signals of the given specification.
    prOutputs ::
      S.Configuration -> S.Specification -> String
    prOutputs c s = case S.outputs c s of
      Left err -> show err
      Right [] -> ""
      Right (x : xr) -> x ++ concatMap ((:) ',' . (:) ' ') xr

-- | Check if 'ltlsynt' is available on path
checkLtlsynt :: FilePath -> IO Bool
checkLtlsynt path = do
  m <- findExecutable path
  return $ isJust m
