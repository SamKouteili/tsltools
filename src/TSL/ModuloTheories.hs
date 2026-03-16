-- | Utilities related to TSLMT.
module TSL.ModuloTheories
  ( theorize,
    parse,
    module TSL.ModuloTheories.Cfg,
    module TSL.ModuloTheories.ConsistencyChecking,
    module TSL.ModuloTheories.Decomposition,
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
import TSL.ModuloTheories.Decomposition (buildDtoList, predicateLiteralsFromSpec)
import TSL.ModuloTheories.Predicates
import qualified TSL.Preprocessor as PP (Specification (..), FunctionDef (..), parse, signal2Smt)
import TSL.ModuloTheories.Sygus
import TSL.ModuloTheories.Theories

theorize :: FilePath -> Int -> String -> IO String
theorize solverPath numModels spec = do
  -- check if ltlsynt is available on path
  ltlsyntAvailable <- checkSolverPath solverPath
  unless ltlsyntAvailable $
    unwrap . genericError $
      "Invalid path to solver: " ++ solverPath

  -- parse and theorize
  (mTheory, defs, tslSpec, specStr) <- parse spec
  case mTheory of
    Nothing -> return specStr
    Just theory -> do
      let cfg = unError $ cfgFromSpec theory tslSpec
          preds = unError $ predicateLiteralsFromSpec theory tslSpec

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
                defs
                preds

          sygusAssumptions :: IO String
          sygusAssumptions =
            extractAssumptions Nothing $
              generateSygusAssumptions
                solverPath
                defs
                cfg
                numModels
                (unError $ buildDtoList theory tslSpec)

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

parse :: String -> IO (Maybe Theory, [DefinedFunction], Specification, String)
parse spec = do
  let linesList = lines spec
      hasTheoryAnnotation = '#' == head (head linesList)
  if hasTheoryAnnotation
    then do
      let theoryLine = head linesList
          restLines = tail linesList
          -- Separate #define lines from the rest
          (defineLines, otherLines) = span isDefineLine restLines
          specStr = unlines otherLines
      theory <- unwrap <$> readTheory $ theoryLine
      -- Parse #define lines using the preprocessor
      defs <- parseDefines theory (unlines (theoryLine : defineLines))
      tslmt <- readTSL specStr >>= unwrap
      return (Just theory, defs, tslmt, specStr)
    else do
      rawTSL <- readTSL spec >>= unwrap
      return (Nothing, [], rawTSL, spec)
  where
    isDefineLine l =
      let stripped = dropWhile (== ' ') l
       in take 7 stripped == "#define"

    parseDefines :: Theory -> String -> IO [DefinedFunction]
    parseDefines theory input = do
      let ppResult = PP.parse input
      case ppResult of
        Left _ -> return []
        Right ppSpec -> return $ extractDefs theory ppSpec

    extractDefs :: Theory -> PP.Specification -> [DefinedFunction]
    extractDefs theory ppSpec =
      let defs = ppSpecDefs ppSpec
       in map (functionDef2Defined theory) defs

    ppSpecDefs :: PP.Specification -> [PP.FunctionDef]
    ppSpecDefs (PP.Specification _ defs _ _) = defs

    functionDef2Defined :: Theory -> PP.FunctionDef -> DefinedFunction
    functionDef2Defined theory (PP.FunctionDef name params body) =
      let sortStr = case theory of
            Nra -> "Real"
            Lia -> "Int"
            _ -> show theory
          paramDecls = unwords $ map (\p -> "(" ++ p ++ " " ++ sortStr ++ ")") params
          smtBody = PP.signal2Smt body
          smtDecl = "(define-fun " ++ name ++ " (" ++ paramDecls ++ ") " ++ sortStr ++ " " ++ smtBody ++ ")"
       in DefinedFunction name smtDecl

-- | Check if the given solver path is valid
checkSolverPath :: FilePath -> IO Bool
checkSolverPath path = do
  m <- findExecutable path
  return $ isJust m
