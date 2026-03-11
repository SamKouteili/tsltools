{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Module      :  TSL.ModuloTheories.Sygus.Assumption
-- Description :  Generate TSL Assumptions from SyGuS results
-- Maintainer  :  Wonhyuk Choi
module TSL.ModuloTheories.Sygus.Assumption
  ( makeAssumption,
  )
where

import Data.List (intersperse)
import TSL.Error (Error)
import TSL.ModuloTheories.Predicates (pred2Tsl)
import TSL.ModuloTheories.Sygus.Common (Dto (..), Temporal (..))
import TSL.ModuloTheories.Sygus.Update (Update (..))

tslAnd :: String
tslAnd = "&&"

updates2Tsl :: (Eq a, Show a) => [[Update a]] -> String
updates2Tsl updates = unwords $ intersperse tslAnd depthAssumptions
  where
    depthAssumptions = zipWith depth2Assumption [0 ..] $ reverse updates

    applyNext :: Int -> String -> String
    applyNext 0 expr = expr
    applyNext depth expr = applyNext (depth - 1) ("X(" ++ expr ++ ")")

    depth2Assumption :: (Show a) => Int -> [Update a] -> String
    depth2Assumption depth depthUpdates = applyNext depth ("(" ++ anded ++ ")")
      where
        anded = unwords $ intersperse tslAnd $ map show depthUpdates

applyTemporal :: Temporal -> String -> String
applyTemporal temporal expr = case temporal of
  Next numNext ->
    let applyN 0 value = value
        applyN depth value = applyN (depth - 1) ("X(" ++ value ++ ")")
     in applyN numNext expr
  Eventually -> "F(" ++ expr ++ ")"

makeAssumption :: Dto -> [[Update String]] -> Either Error String
makeAssumption (Dto _ pre post temporal) updates =
  Right $
    unwords
      [ "G",
        "(", -- GLOBALLY
        "(", -- PRE + UPDATES
        pred2Tsl pre,
        updateTerm,
        ")", -- PRE + UPDATES
        "->",
        applyTemporal temporal ("(" ++ pred2Tsl post ++ ")"),
        ")", -- GLOBALLY
        ";"
      ]
  where
    weakUntil = " W "
    updateChain = updates2Tsl updates
    updateTerm =
      case temporal of
        Eventually
          | null updateChain -> ""
          | otherwise -> unwords [tslAnd, updateChain, weakUntil ++ pred2Tsl post]
        _ ->
          if null updateChain
            then ""
            else unwords [tslAnd, updateChain]
