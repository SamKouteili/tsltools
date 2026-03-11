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

import Control.Monad (filterM)
import Control.Monad.Trans.Except
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

generateConsistencyAssumptions ::
  FilePath ->
  [DefinedFunction] ->
  [TheoryPredicate] ->
  [ExceptT Error IO String]
generateConsistencyAssumptions path defs preds =
  map (fmap fst . consistencyChecking path defs) (consistencyCombos preds)

consistencyDebug ::
  FilePath ->
  [DefinedFunction] ->
  [TheoryPredicate] ->
  [ExceptT Error IO ConsistencyDebugInfo]
consistencyDebug path defs preds =
  map (fmap snd . consistencyChecking path defs) (consistencyCombos preds)

consistencyCombos :: [TheoryPredicate] -> [TheoryPredicate]
consistencyCombos [] = []
consistencyCombos preds =
  let theory = predTheory (head preds)
   in map (andPredsOrTrue theory) $ powerset preds

powerset :: [a] -> [[a]]
powerset = filterM (const [True, False])

andPredsOrTrue :: Theory -> [TheoryPredicate] -> TheoryPredicate
andPredsOrTrue theory = \case
  [] -> PTrue theory
  [x] -> x
  (x : xs) -> AndPLit x (andPredsOrTrue theory xs)

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
