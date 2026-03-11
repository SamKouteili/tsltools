{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Module      :  TSL.ModuloTheories.Sygus
-- Description :  Master module for Sygus
-- Maintainer  :  Wonhyuk Choi
module TSL.ModuloTheories.Sygus
  ( generateSygusAssumptions,
    SygusDebugInfo (..),
    sygusDebug,
  )
where

import Control.Monad (liftM2)
import Control.Monad.Trans.Except
import TSL.Error (Error, errSygus)
import TSL.ModuloTheories.Cfg (Cfg)
import TSL.ModuloTheories.Debug (IntermediateResults (..))
import TSL.ModuloTheories.Solver (runSygusQuery)
import TSL.ModuloTheories.Sygus.Assumption (makeAssumption)
import TSL.ModuloTheories.Sygus.Common
  ( Dto (..),
    Model,
    Temporal (..),
    Term,
  )
import TSL.ModuloTheories.Sygus.Parser (parseSygusResult)
import TSL.ModuloTheories.Sygus.Query (generateSygusQuery)
import TSL.ModuloTheories.Sygus.Recursion
  ( findRecursion,
    generatePbeModels,
  )
import TSL.ModuloTheories.Sygus.Update (Update, term2Updates)
import TSL.ModuloTheories.Theories (DefinedFunction, TheorySymbol, sygus2Supported)

data SygusDebugInfo
  = NextDebug IntermediateResults String
  | EventuallyDebug [(IntermediateResults, IntermediateResults)] String
  deriving (Show)

generateUpdates ::
  FilePath ->
  [DefinedFunction] ->
  Cfg ->
  Maybe Int ->
  [Model TheorySymbol] ->
  Dto ->
  ExceptT Error IO ([[Update String]], IntermediateResults)
generateUpdates solverPath defs cfg depth models dto = liftM2 (,) updates debugInfo
  where
    query :: Either Error String
    query = generateSygusQuery defs cfg models dto

    result :: ExceptT Error IO String
    result = except query >>= (runSygusQuery solverPath depth)

    term :: ExceptT Error IO (Term String)
    term = do
      value <- result
      case parseSygusResult (head (lines value)) of
        Left err -> except $ Left err
        Right term -> return term

    updates :: ExceptT Error IO [[Update String]]
    updates = term2Updates <$> term

    debugInfo :: ExceptT Error IO IntermediateResults
    debugInfo = IntermediateResults (show dto) <$> except query <*> result

generateAssumption ::
  FilePath ->
  [DefinedFunction] ->
  Cfg ->
  Dto ->
  ExceptT Error IO (String, SygusDebugInfo)
generateAssumption solverPath defs cfg dto =
  if not $ sygus2Supported $ theory dto
    then except unsupportedError
    else case temporal dto of
      (Next n)
        | n == 0 -> do
            let debugInfo = IntermediateResults (show dto) "" "no-sygus"
            assumption <- makeAssumption' dto []
            let debugInfo' = NextDebug debugInfo assumption
            return (assumption, debugInfo')
        | otherwise -> do
            (updates, debugInfo) <- genNextUpdates n
            let actualDepth = length updates
            if actualDepth /= n
              then except $ errSygus $ "SyGuS depth mismatch: expected " ++ show n ++ ", got " ++ show actualDepth
              else do
                assumption <- makeAssumption' dto updates
                let debugInfo' = NextDebug debugInfo assumption
                return (assumption, debugInfo')
      Eventually -> do
        pbeResults <- generatePbeModels solverPath dto
        let (pbeModels, pbeInfos) = unzip pbeResults

        subqueryResults <- mapM genEventuallyUpdates pbeModels
        let (subqueryUpdates, subqueryInfos) = unzip subqueryResults

        updates <- except $ findRecursion subqueryUpdates
        assumption <- makeAssumption' dto updates
        let debugInfo = EventuallyDebug (zip pbeInfos subqueryInfos) assumption
        return (assumption, debugInfo)
  where
    genUpdates depth = (flip (generateUpdates solverPath defs cfg depth)) dto
    genNextUpdates depth = genUpdates (Just depth) []
    genEventuallyUpdates = genUpdates Nothing
    unsupportedError =
      errSygus $
        "Theory "
          ++ show (theory dto)
          ++ " not supported in the Sygus 2 Standard"
    makeAssumption' dto' updates =
      except $ makeAssumption dto' updates

generateSygusAssumptions ::
  FilePath ->
  [DefinedFunction] ->
  Cfg ->
  [Dto] ->
  [ExceptT Error IO String]
generateSygusAssumptions solverPath defs cfg dtos =
  map (fmap fst) $
    generateAssumption solverPath defs cfg
      <$> dtos

sygusDebug ::
  FilePath ->
  [DefinedFunction] ->
  Cfg ->
  [Dto] ->
  [ExceptT Error IO SygusDebugInfo]
sygusDebug solverPath defs cfg dtos =
  map (fmap snd) $
    generateAssumption solverPath defs cfg
      <$> dtos
