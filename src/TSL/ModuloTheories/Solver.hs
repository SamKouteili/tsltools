{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      :  TSL.ModuloTheories.Solver
-- Description :  Utilities to send SMT and SyGuS problems to a solver
--                and parse their results.
--                The choice of solver is extensible,
--                but currently it is hardcoded as CVC5 for now.
-- Maintainer  :  Wonhyuk Choi
module TSL.ModuloTheories.Solver (solveSat, runGetModel, runSygusQuery) where

import Control.Monad.Trans.Except
import Data.List (isInfixOf)
import qualified Data.Text as Text
import System.Exit (ExitCode (..))
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)
import TSL.Error (Error, errSolver, errSygus)

strip :: String -> String
strip = Text.unpack . Text.strip . Text.pack

isSat :: String -> Either Error Bool
isSat "sat" = Right True
isSat "unsat" = Right False
isSat err = errSolver err

runSolver :: FilePath -> [String] -> String -> ExceptT Error IO String
runSolver solverPath args query = do
  -- fileCount <- liftIO $ getDirectoryContents "tmp"
  -- let logName = "tmp/tmp_" ++ show (length fileCount `div` 2)
  -- liftIO $ writeFile (logName ++ ".smt2") query
  -- liftIO $ writeFile (logName ++ "_args.txt") $ unlines args
  result <- ExceptT $ do
    mResult <- timeout config_SOLVER_TIMEOUT_US $
      readProcessWithExitCode solverPath args query
    pure $ case mResult of
      Nothing ->
        errSolver $
          "Timed out after "
            ++ show (config_SOLVER_TIMEOUT_US `div` 1000000)
            ++ " seconds: "
            ++ solverPath
      Just solverResult -> Right solverResult
  parseResult result
  where
    -- Keep individual solver calls bounded so one hard SyGuS/SMT query
    -- does not block the whole TSL-MT pipeline.
    config_SOLVER_TIMEOUT_US :: Int
    config_SOLVER_TIMEOUT_US = 10 * 1000000

    parseResult :: (ExitCode, String, String) -> ExceptT Error IO String
    parseResult (exitCode, stdout, stderr) = case exitCode of
      ExitSuccess -> return stdout
      ExitFailure code -> except $ errSolver errMsg
        where
          errMsg = show code ++ " >> " ++ stderr ++ "\n" ++ stdout

solveSat :: FilePath -> String -> ExceptT Error IO Bool
solveSat solverPath = (=<<) toBoolean . runSolver solverPath smt2
  where
    smt2 = ["--lang=smt2"]
    toBoolean = except . isSat . strip

runGetModel :: FilePath -> String -> ExceptT Error IO String
runGetModel solverPath = runSolver solverPath args
  where
    args = ["--lang=smt2"]

runSygusQuery :: FilePath -> Int -> String -> ExceptT Error IO String
runSygusQuery solverPath depth = (=<<) getResult . runSolver solverPath args
  where
    args = depthLimit : ["-o", "sygus-sol-gterm", "--lang=sygus2"]
    depthLimit = "--sygus-abort-size=" ++ show depth
    getResult result =
      except $
        if "error" `isInfixOf` result
          then errSygus result
          else if "infeasible" `isInfixOf` result
            then errSygus "SyGus query is infeasible"
            else Right result
