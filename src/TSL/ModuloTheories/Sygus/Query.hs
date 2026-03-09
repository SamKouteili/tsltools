{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Module      :  TSL.ModuloTheories.Sygus.Query
-- Description :  Generates SyGuS problems from a Data Transformation Obligation.
-- Maintainer  :  Wonhyuk Choi
module TSL.ModuloTheories.Sygus.Query (generateSygusQuery) where

import Data.List (nub)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import TSL.Error (Error, errSygus)
import TSL.ModuloTheories.Cfg
  ( Cfg (..),
    extendCfg,
    outputSignals,
  )
import TSL.ModuloTheories.Predicates
  ( TheoryPredicate,
    pred2Smt,
    predReplacedSmt,
    predSignals,
  )
import TSL.ModuloTheories.Sygus.Common
  ( Dto (..),
    Model,
    parenthize,
    targetPostfix,
  )
import TSL.ModuloTheories.Theories
  ( DefinedFunction (..),
    TAst,
    TheorySymbol,
    makeSignal,
    smtSortDecl,
    symbolTheory,
    symbolType,
    tast2Smt,
    tastSignals,
  )

minitab :: Int -> String -> String
minitab n = (++) (replicate (2 * n) ' ')

functionName :: String
functionName = "function"

declareVar :: TheorySymbol -> String
declareVar symbol = parenthize 1 $ unwords [show symbol, symbolType symbol]

dto2Sygus :: [TheorySymbol] -> TheorySymbol -> [Model TheorySymbol] -> Dto -> String
dto2Sygus extraParams synthTarget models (Dto _ pre post) =
  unlines
    [ "(constraint",
      forallExpr,
      ")"
    ]
  where
    paren1 = parenthize 1
    precondition = paren1 $ unwords $ "and" : (pred2Smt pre) : (map show models)
    -- Apply the synthesized function to the target signal plus any extra
    -- parameters (free-variable input signals appearing in the update rule).
    fApplied = paren1 $ unwords $ [functionName, show synthTarget] ++ map show extraParams
    postcondition = predReplacedSmt synthTarget fApplied post
    forallExpr = unlines [forallDecl, forallBody, minitab 1 ")"]
    -- Quantify every signal that can appear in the DTO constraint:
    -- signals from pre/post predicates plus any extra synth-fun parameters
    -- (free-variable input signals like x in [y <- f x]) so that the
    -- function call (function y x) is well-scoped inside the forall.
    varDecls = paren1 $ unwords $ map declareVar allSignals
    allSignals = nub $ predSignals pre ++ predSignals post ++ extraParams
    forallDecl = minitab 1 $ "(forall " ++ varDecls
    forallBody =
      unlines $
        map
          (minitab 2)
          [ "(=>",
            minitab 1 precondition,
            minitab 1 postcondition,
            ")"
          ]

getSygusTargets :: TheoryPredicate -> Cfg -> [TheorySymbol]
getSygusTargets postCondition cfg = Set.toList intersection
  where
    outputs = outputSignals cfg
    postSignals = Set.fromList $ predSignals postCondition
    intersection = Set.intersection outputs postSignals

-- | Picks one signal to synthesize SyGuS for.
-- Unfortunately, the current procedure only allows synthesis
-- of one single function. More info:
-- /docs/tslmt2tsl-limitations.md#simultaneous-updates
pickTarget :: [TheorySymbol] -> TheorySymbol
pickTarget = head

getProductionRules :: TheorySymbol -> Cfg -> Maybe [TAst]
getProductionRules nonterminal cfg = Map.lookup nonterminal (grammar cfg)

nonterminalsUsed :: TheorySymbol -> Cfg -> Set TheorySymbol
nonterminalsUsed symbol cfg = helper symbol Set.empty
  where
    helper :: TheorySymbol -> Set TheorySymbol -> Set TheorySymbol
    helper symbol set =
      case getProductionRules symbol cfg of
        Nothing -> set
        Just rules -> Set.union set $ Set.fromList $ concat $ map tastSignals rules

productionRules2Sygus :: TheorySymbol -> [TAst] -> String
productionRules2Sygus nonterminal rules =
  unlines
    [ minitab 2 $ "(" ++ declaration,
      expansion,
      minitab 2 ")"
    ]
  where
    declaration = unwords [show nonterminal, symbolType nonterminal]
    expansion = minitab 3 $ parenthize 1 rulesSygus
    rulesSygus = unwords $ map tast2Smt rules

syntaxConstraint :: [TheorySymbol] -> TheorySymbol -> Cfg -> String
syntaxConstraint extraParams functionInput cfg =
  unlines
    [ funDeclComment,
      "(" ++ functionDeclaration,
      varDeclComment,
      varDecls,
      "",
      minitab 1 "(",
      unlines $ fmap sygusGrammar nonterminals,
      minitab 1 ")",
      ")"
    ]
  where
    sygusGrammar :: TheorySymbol -> String
    sygusGrammar nonterminal =
      case (getProductionRules nonterminal cfg') of
        Nothing -> minitab 2 $ ";; No grammar for " ++ show nonterminal ++ "\n"
        Just rules -> productionRules2Sygus nonterminal rules

    -- Extra parameters (free-variable input signals) are declared alongside
    -- the main target parameter so grammar rules can reference them directly.
    functionDeclaration =
      unwords
        [ "synth-fun",
          functionName,
          "(" ++ unwords (mainParam : extraParamDecls) ++ ")",
          varType
        ]
      where
        mainParam = "( " ++ inputName ++ " " ++ varType ++ " )"
        extraParamDecls = map (\s -> "( " ++ show s ++ " " ++ symbolType s ++ " )") extraParams
    -- Compute the candidate nonterminals: always include functionInput itself
    -- (so constant-only updates like [y <- 3.0] get at least one nonterminal),
    -- plus any signals that appear inside its production rules.
    -- Then filter to only those that actually have production rules in cfg'
    -- (the extended grammar), so that symbols like free variables (x) or
    -- defined functions (f) used in updates don't appear as nonterminals
    -- without expansion rules, which CVC5 rejects.
    nonterminals =
      filter (\sym -> case getProductionRules sym cfg' of Nothing -> False; Just _ -> True) $
        Set.toList $ Set.insert functionInput $ nonterminalsUsed functionInput cfg
    varDecls = parenthize 1 $ unwords $ map declareVar nonterminals
    varType = symbolType functionInput
    inputName = show functionInput ++ targetPostfix
    inputTast = makeSignal (symbolTheory functionInput) inputName
    cfg' = extendCfg (functionInput, inputTast) cfg

    funDeclComment = "\r\n;; Name and signature of the function to be synthesized"
    varDeclComment = "\r\n;; Declare the nonterminals used in the grammar"

-- | Signals that appear in the production rules of @synthTarget@ but have no
-- CFG rules of their own (so cannot be grammar nonterminals) and are not
-- defined functions.  These must be declared as extra @synth-fun@ parameters
-- so CVC5 can reference them inside grammar production rules.
computeExtraParams :: [DefinedFunction] -> TheorySymbol -> Cfg -> [TheorySymbol]
computeExtraParams defs synthTarget cfg =
  filter isExtraParam $ Set.toList $ nonterminalsUsed synthTarget cfg
  where
    hasRulesInCfg sym = case Map.lookup sym (grammar cfg) of
      Nothing -> False
      Just _ -> True
    isDefinedFunc sym = show sym `elem` map dfName defs
    isExtraParam sym = not (hasRulesInCfg sym) && not (isDefinedFunc sym)

generateSygusQuery :: [DefinedFunction] -> Cfg -> [Model TheorySymbol] -> Dto -> Either Error String
generateSygusQuery defs cfg models dto@(Dto theory _ post) =
  if null sygusTargets
    then errSygus $ "Empty Query for " ++ show dto
    else Right query
  where
    sygusTargets = getSygusTargets post cfg
    synthTarget = pickTarget sygusTargets
    extraParams = computeExtraParams defs synthTarget cfg
    grammar = syntaxConstraint extraParams synthTarget cfg
    constraint = dto2Sygus extraParams synthTarget models dto
    declTheory = "(set-logic " ++ show theory ++ ")"
    checkSynth = "(check-synth)"
    sortDecl = smtSortDecl theory
    defineFuns = unlines $ map dfSmtDecl defs
    query =
      unlines
        [ declTheory,
          sortDecl,
          defineFuns,
          grammar,
          constraint,
          checkSynth
        ]
