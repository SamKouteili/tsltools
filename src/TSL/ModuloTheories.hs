-- | Utilities related to TSLMT.
module TSL.ModuloTheories
  ( theorize,
    parse,
    module TSL.ModuloTheories.Cfg,
    module TSL.ModuloTheories.ConsistencyChecking,
    module TSL.ModuloTheories.Predicates,
    module TSL.ModuloTheories.Sygus,
    module TSL.ModuloTheories.Theories,
  )
where

import Control.Monad (unless, when)
import Control.Monad.Trans.Except
import Data.Maybe (isJust)
import System.Directory (findExecutable)
import System.IO (hPutStrLn, stderr)
import TSL.Base.Reader (readTSL)
import TSL.Base.Specification (Specification)
import TSL.Error (genericError, unwrap)
import TSL.ModuloTheories.Cfg
import TSL.ModuloTheories.ConsistencyChecking
import TSL.ModuloTheories.Predicates
import TSL.ModuloTheories.Sygus
import TSL.ModuloTheories.Theories

theorize :: FilePath -> String -> IO String
theorize solverPath spec = do
  -- check if ltlsynt is available on path
  ltlsyntAvailable <- checkSolverPath solverPath
  unless ltlsyntAvailable $
    unwrap . genericError $
      "Invalid path to solver: " ++ solverPath

  -- parse and theorize
  (mTheory, tslSpec, specStr) <- parse spec
  case mTheory of
    Nothing -> return specStr
    Just theory -> do
      let cfg = unError $ cfgFromSpec theory tslSpec
          preds = unError $ predsFromSpec theory tslSpec

          mkAlwaysAssume :: String -> String
          mkAlwaysAssume assumptions =
            unlines
              [ "always assume {",
                assumptions,
                "}"
              ]

          extractAssumptions :: (Show e) => Maybe Int -> [ExceptT e IO String] -> IO String
          extractAssumptions maxAssumptions results = do
            (assumptions, skipped) <- gather results []
            when (skipped > 0) $
              hPutStrLn stderr $
                "[TSL-MT] skipped " ++ show skipped ++ " assumptions"
            return $ unlines assumptions
            where
              reachedCap kept =
                case maxAssumptions of
                  Just n -> kept >= n
                  Nothing -> False

              gather [] kept = return (reverse kept, 0)
              gather pending kept
                | reachedCap (length kept) =
                    return (reverse kept, length pending)
              gather (nextResult : rest) kept = do
                runResult <- runExceptT nextResult
                case runResult of
                  Right assumption -> gather rest (assumption : kept)
                  Left _ -> do
                    (assumptions, skipped) <- gather rest kept
                    return (assumptions, skipped + 1)

          consistencyAssumptions :: IO String
          consistencyAssumptions =
            extractAssumptions Nothing $
              generateConsistencyAssumptions
                solverPath
                preds

          sygusAssumptions :: IO String
          sygusAssumptions =
            extractAssumptions (Just 8) $
              generateSygusAssumptions
                solverPath
                cfg
                (buildDtoList preds)

          assumptionsBlock :: IO String
          assumptionsBlock =
            mkAlwaysAssume
              <$> ( (++)
                      <$> consistencyAssumptions
                      <*> sygusAssumptions
                  )
      (++ specStr) <$> assumptionsBlock
  where
    unError :: (Show a) => Either a b -> b
    unError = \case
      Left err -> error $ show err
      Right val -> val

parse :: String -> IO (Maybe Theory, Specification, String)
parse spec = do
  let linesList = lines spec
      hasTheoryAnnotation = '#' == head (head linesList)
  if hasTheoryAnnotation
    then do
      let specStr = unlines $ tail linesList -- FIXME: unlines.lines is computationally wasteful
      theory <- unwrap <$> readTheory $ head linesList
      tslmt <- readTSL specStr >>= unwrap
      return (Just theory, tslmt, specStr)
    else do
      rawTSL <- readTSL spec >>= unwrap
      return (Nothing, rawTSL, spec)

-- | Check if the given solver path is valid
checkSolverPath :: FilePath -> IO Bool
checkSolverPath path = do
  m <- findExecutable path
  return $ isJust m
