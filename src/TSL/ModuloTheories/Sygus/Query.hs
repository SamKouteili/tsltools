{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Module      :  TSL.ModuloTheories.Sygus.Query
-- Description :  Generates SyGuS problems from a Data Transformation Obligation.
-- Maintainer  :  Wonhyuk Choi
module TSL.ModuloTheories.Sygus.Query (generateSygusQuery) where

import Data.List (nub, partition)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import TSL.Base.Ast (AstInfo (..), SymbolInfo (..), deduplicate, (+++))
import TSL.Error (Error, errSygus)
import TSL.ModuloTheories.Cfg
  ( Cfg (..),
    extendCfg,
    outputSignals,
  )
import TSL.ModuloTheories.Predicates
  ( TheoryPredicate,
    pred2Smt,
    predInfo,
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
    Theory,
    TheorySymbol,
    isUninterpreted,
    makeSignal,
    read2Symbol,
    replaceTAst,
    smtSortDecl,
    symbol2Smt,
    symbolTheory,
    symbolType,
    tast2Smt,
    tastInfo,
    tastSignals,
  )

minitab :: Int -> String -> String
minitab n = (++) (replicate (2 * n) ' ')

functionName :: String
functionName = "function"

declareVar :: TheorySymbol -> String
declareVar symbol = parenthize 1 $ unwords [show symbol, symbolType symbol]

dto2Sygus :: TheorySymbol -> [Model TheorySymbol] -> Dto -> String
dto2Sygus synthTarget models (Dto _ pre post _) =
  unlines
    [ "(constraint",
      forallExpr,
      ")"
    ]
  where
    paren1 = parenthize 1
    precondition = paren1 $ unwords $ "and" : (pred2Smt pre) : (map show models)
    fApplied = paren1 $ unwords [functionName, show synthTarget]
    postcondition = predReplacedSmt synthTarget fApplied post
    forallExpr = unlines [forallDecl, forallBody, minitab 1 ")"]
    -- Quantify every signal that can appear in the DTO constraint.
    -- Restricting this to post signals causes undeclared-variable errors
    -- whenever the precondition introduces extra symbols.
    varDecls = paren1 $ unwords $ map declareVar allSignals
    allSignals = nub $ predSignals pre ++ predSignals post
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

syntaxConstraint :: TheorySymbol -> Cfg -> String
syntaxConstraint functionInput cfg =
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

    functionDeclaration =
      unwords
        [ "synth-fun",
          functionName,
          "((",
          inputName,
          varType,
          "))",
          varType
        ]
    nonterminals = Set.toList $ nonterminalsUsed functionInput cfg
    varDecls = parenthize 1 $ unwords $ map declareVar nonterminals
    varType = symbolType functionInput
    inputName = show functionInput ++ targetPostfix
    inputTast = makeSignal (symbolTheory functionInput) inputName
    -- Build grammar like TeMoS (PLDI'22): for each production rule,
    -- include both the original (recursive, nonterminal references stay)
    -- and a variant with the nonterminal replaced by the synth-fun input
    -- (terminal base case). Do NOT add bare identity as a standalone rule.
    inputSymbol = case read2Symbol (symbolTheory functionInput) inputName of
      Right s -> s
      Left _ -> error "Failed to create input symbol"
    cfg' = addTerminalVariants functionInput inputSymbol cfg

    -- For each rule of the target nonterminal, add a variant where
    -- occurrences of the nonterminal are replaced with the input variable.
    addTerminalVariants :: TheorySymbol -> TheorySymbol -> Cfg -> Cfg
    addTerminalVariants nt inputSym (Cfg g) =
      case Map.lookup nt g of
        Nothing -> Cfg g
        Just rules ->
          let terminalRules = map (replaceTAst (nt, inputSym)) rules
              allRules = rules ++ terminalRules
           in Cfg $ Map.insert nt allRules g


    funDeclComment = "\r\n;; Name and signature of the function to be synthesized"
    varDeclComment = "\r\n;; Declare the nonterminals used in the grammar"

-- | Collect AstInfo from all production rules in the CFG grammar.
cfgInfo :: Cfg -> AstInfo TheorySymbol
cfgInfo cfg =
  foldl (+++) (AstInfo [] [] []) $
    concatMap (map tastInfo) $ Map.elems (grammar cfg)

-- | Generate declare-const and declare-fun statements for all symbols
-- that appear in the grammar and DTO constraints but are not already
-- declared as synth-fun inputs, forall-quantified variables, or defined functions.
sygusDeclarations :: Theory -> [DefinedFunction] -> TheorySymbol -> Dto -> Cfg -> String
sygusDeclarations theory defs synthTarget (Dto _ pre post _) cfg =
  unlines [defineFuns, varDecls, funcDecls, predDecls]
  where
    -- Collect all symbols from grammar rules and pre/post conditions
    allInfo = deduplicate $ cfgInfo cfg +++ predInfo pre +++ predInfo post
    AstInfo vars funcs preds = allInfo

    -- Names to exclude: synth-fun input, forall-quantified vars, defined functions
    definedNames = map dfName defs
    synthInputName = symbol2Smt synthTarget ++ targetPostfix
    forallNames = map symbol2Smt $ nub $ predSignals pre ++ predSignals post
    excludeNames = synthInputName : forallNames ++ definedNames

    defineFuns = unlines $ map dfSmtDecl defs

    -- Nullary functions (arity 0) are constants — declare them as such
    (nullaryFuncs, realFuncs) = partition (\(SymbolInfo _ a) -> a == 0) funcs

    -- Declare constants: vars + nullary functions that aren't excluded
    allConsts = vars ++ nullaryFuncs
    varDecls = unlines $ map declConst $ filter (notExcluded . symbol) allConsts
    funcDecls = unlines $ map declFunc realFuncs
    predDecls = unlines $ map declPred preds

    notExcluded sym = symbol2Smt sym `notElem` excludeNames
    symbol (SymbolInfo x _) = x

    declConst (SymbolInfo x _) =
      "(declare-const " ++ symbol2Smt x ++ " " ++ symbolType x ++ ")"

    declareFun retType (SymbolInfo f arity)
      | not (isUninterpreted f) = ""
      | symbol2Smt f `elem` excludeNames = ""
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

generateSygusQuery :: [DefinedFunction] -> Cfg -> [Model TheorySymbol] -> Dto -> Either Error String
generateSygusQuery defs cfg models dto@(Dto theory _ post _) =
  if null sygusTargets
    then errSygus $ "Empty Query for " ++ show dto
    else Right query
  where
    sygusTargets = getSygusTargets post cfg
    synthTarget = pickTarget sygusTargets
    grammarBlock = syntaxConstraint synthTarget cfg
    constraint = dto2Sygus synthTarget models dto
    declTheory = "(set-logic " ++ show theory ++ ")"
    checkSynth = "(check-synth)"
    sortDecl = smtSortDecl theory
    declarations = sygusDeclarations theory defs synthTarget dto cfg
    query =
      unlines
        [ declTheory,
          sortDecl,
          declarations,
          grammarBlock,
          constraint,
          checkSynth
        ]
