{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

-- Module      :  TSL.ModuloTheories.ConsistencyChecking
-- Description :  Adds partial semantics back to uninterpreted functions by checking which combinations
--                of uninterpreted predicates are satisfiable.  To avoid an exponential blow‑up in SMT
--                calls, we now cap the number of combinations examined.
-- Maintainer  :  Wonhyuk Choi
module TSL.ModuloTheories.ConsistencyChecking
  ( generateConsistencyAssumptions,
    consistencyDebug,
    ConsistencyDebugInfo (..),
  )
where

import Control.Monad.Trans.Except
import qualified Data.List as L
import Debug.Trace (trace)
import TSL.Base.Ast (AstInfo (..), SymbolInfo (..), deduplicate)
import TSL.Error (Error, errConsistency)
import TSL.ModuloTheories.Debug (IntermediateResults (..))
import TSL.ModuloTheories.Predicates
  ( TheoryPredicate (..),
    pred2Smt,
    pred2Tsl,
    predInfo,
    predTheory,
  )
import TSL.ModuloTheories.Solver (solveSat)
import TSL.ModuloTheories.Theories
  ( DefinedFunction (..),
    Theory,
    TheorySymbol,
    isUninterpreted,
    smtSortDecl,
    symbol2Smt,
    symbolType,
  )

-- | Hard cap on how many predicate combinations we send to the SMT solver.
--    This prevents run‑away exponential behaviour when many uninterpreted
--    predicates appear in the spec.  Adjust as needed or expose it as a CLI flag.
--  this number can be changed based on the problem, but even for simple synthesis problems the
--  number of predicates being checked was always become 2^n. This simplifies while getting the correct answer
config_MAX_CONSISTENCY_CHECKS :: Maybe Int
config_MAX_CONSISTENCY_CHECKS = Just 30

generateConsistencyAssumptions ::
  FilePath ->
  [DefinedFunction] ->
  [TheoryPredicate] ->
  [ExceptT Error IO String]
generateConsistencyAssumptions path defs preds =
  map (fmap fst . consistencyChecking path defs) limitedCombos
  where
    combos = consistencyCombos preds
    limitedCombos = case config_MAX_CONSISTENCY_CHECKS of
      Just n -> take n combos
      Nothing -> combos

consistencyDebug ::
  FilePath ->
  [DefinedFunction] ->
  [TheoryPredicate] ->
  [ExceptT Error IO ConsistencyDebugInfo]
consistencyDebug path defs preds =
  map (fmap snd . consistencyChecking path defs) limitedCombos
  where
    combos = consistencyCombos preds
    limitedCombos = case config_MAX_CONSISTENCY_CHECKS of
      Just n -> take n combos
      Nothing -> combos

consistencyCombos :: [TheoryPredicate] -> [TheoryPredicate]
consistencyCombos preds = singles ++ pairs
  where
    samePred x y = show x == show y
    literals = L.nubBy samePred (preds ++ map NotPLit preds)
    singles = literals
    pairs =
      [ AndPLit p q
        | (idx, p) <- zip [0 :: Int ..] literals,
          q <- drop (idx + 1) literals
      ]

pred2Assumption :: TheoryPredicate -> String
pred2Assumption p = "G " ++ pred2Tsl (NotPLit p) ++ ";"

data ConsistencyDebugInfo = ConsistencyDebugInfo IntermediateResults String

instance Show ConsistencyDebugInfo where
  show (ConsistencyDebugInfo results assumption) =
    "ConsistencyDebugInfo {"
      ++ "\n  results: "
      ++ show results
      ++ ",\n  assumption: "
      ++ assumption
      ++ "\n}"

consistencyChecking ::
  FilePath ->
  [DefinedFunction] ->
  TheoryPredicate ->
  ExceptT Error IO (String, ConsistencyDebugInfo)
consistencyChecking solverPath defs pred = do
  let query = pred2SmtQuery defs pred
  isSat <- solveSat solverPath query
  if isSat
    then
      except $
        errConsistency $
          "Predicate "
            ++ show pred
            ++ " is satisfiable.  No new assumption added."
    else do
      let assumption = pred2Assumption pred
          intermediateResults = IntermediateResults (show pred) query (show isSat)
          debugInfo = ConsistencyDebugInfo intermediateResults assumption
      trace ("[Consistency] adding assumption for " ++ show pred) $ return ()
      return (assumption, debugInfo)

pred2SmtQuery :: [DefinedFunction] -> TheoryPredicate -> String
pred2SmtQuery defs p = unlines [smtDeclarations, assertion, checkSat]
  where
    smtDeclarations = smtDecls (predTheory p) defs $ deduplicate $ predInfo p
    assertion = "(assert " ++ pred2Smt p ++ ")"
    checkSat = "(check-sat)"

smtDecls :: Theory -> [DefinedFunction] -> AstInfo TheorySymbol -> String
smtDecls theory defs (AstInfo vars funcs preds) =
  unlines [logic, sortDecl, defineFuns, varDecls, funcDecls, predDecls]
  where
    logic = "(set-logic " ++ show theory ++ ")"
    sortDecl = smtSortDecl theory
    definedNames = map dfName defs
    defineFuns = unlines $ map dfSmtDecl defs
    varDecls = unlines $ map declConst $ filter (notDefined . symbol) vars
    funcDecls = unlines $ map declFunc funcs
    predDecls = unlines $ map declPred preds

    notDefined sym = symbol2Smt sym `notElem` definedNames

    symbol (SymbolInfo x _) = x

    declConst (SymbolInfo x _) =
      "(declare-const " ++ symbol2Smt x ++ " " ++ symbolType x ++ ")"

    declareFun retType (SymbolInfo f arity)
      | not (isUninterpreted f) = ""
      | otherwise =
          unwords
            [ "(declare-fun",
              symbol2Smt f,
              "(",
              unwords $ replicate arity $ show theory,
              ")",
              retType ++ ")"
            ]
    declFunc = declareFun (show theory)
    declPred = declareFun "Bool"
