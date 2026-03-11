{-# LANGUAGE LambdaCase #-}

-- |
-- Module      :  TSL.ModuloTheories.Decomposition
-- Description :  Paper-faithful syntactic decomposition for TSL-MT (Algorithm 1).
-- Maintainer  :  Wonhyuk Choi
module TSL.ModuloTheories.Decomposition
  ( buildDtoList,
    predicateLiteralsFromSpec,
  )
where

import Control.Monad (filterM)
import Data.List (nubBy)
import TSL.Base.Ast (fromPredicateTerm)
import TSL.Base.Logic (Formula (..), PredicateTerm, toNNF)
import TSL.Base.Specification (Specification (..), toFormula)
import TSL.Base.SymbolTable (Id, SymbolTable (..))
import TSL.Base.Types (arity)
import TSL.Error (Error)
import TSL.ModuloTheories.Predicates (TheoryPredicate (..))
import TSL.ModuloTheories.Sygus.Common (Dto (..))
import qualified TSL.ModuloTheories.Sygus.Common as Sygus
import TSL.ModuloTheories.Theories
  ( Theory,
    applySemantics,
  )

data Literal a
  = Pos (PredicateTerm a)
  | Neg (PredicateTerm a)
  deriving (Eq)

data Frame
  = BoolFrame
  | NextFrame
  | UntilLeft
  | UntilRight
  | ReleaseLeft
  | ReleaseRight

literalEq :: Eq a => Literal a -> Literal a -> Bool
literalEq = (==)

postEq :: Eq a => (Sygus.Temporal, Literal a) -> (Sygus.Temporal, Literal a) -> Bool
postEq (t1, p1) (t2, p2) = t1 == t2 && p1 == p2

-- | Extract all predicate literals (with polarity) from a specification.
predicateLiteralsFromSpec :: Theory -> Specification -> Either Error [TheoryPredicate]
predicateLiteralsFromSpec theory spec = do
  (nnf, arityFn, unhash) <- nnfFromSpec spec
  let literals = nubBy literalEq $ collectLiterals nnf
  traverse (literalToTheory theory arityFn unhash) literals

-- | Build the full DTO list per Algorithm 1 (powerset of pre/post).
buildDtoList :: Theory -> Specification -> Either Error [Dto]
buildDtoList theory spec = do
  (nnf, arityFn, unhash) <- nnfFromSpec spec
  let literals = nubBy literalEq $ collectLiterals nnf
      postLits = nubBy postEq $ collectPostconditions nnf

  prePreds <- traverse (literalToTheory theory arityFn unhash) literals
  postPreds <- traverse (postToTheory theory arityFn unhash) postLits

  let preCombos = powerset prePreds
      postCombos = powerset postPreds
      mkPre = andPredsOrTrue theory
      mkPost = combinePostconds theory

  return
    [ Dto
        { theory = theory,
          preCondition = mkPre preCombo,
          postCondition = postPred,
          temporal = temporal
        }
      | preCombo <- preCombos,
        postCombo <- postCombos,
        let (temporal, postPred) = mkPost postCombo
    ]

-- | Compute NNF of the full spec formula and provide the arity function.
nnfFromSpec :: Specification -> Either Error (Formula Id, Id -> Int, Id -> String)
nnfFromSpec spec = do
  let unhash = stName (symboltable spec)
      arityFn = arity . stType (symboltable spec)
      formula = toFormula (assumptions spec) (guarantees spec)
  nnf <- toNNF formula
  return (nnf, arityFn, unhash)

collectLiterals :: Formula a -> [Literal a]
collectLiterals = \case
  Check p -> [Pos p]
  Not (Check p) -> [Neg p]
  And xs -> concatMap collectLiterals xs
  Or xs -> concatMap collectLiterals xs
  Next x -> collectLiterals x
  Until x y -> collectLiterals x ++ collectLiterals y
  Release x y -> collectLiterals x ++ collectLiterals y
  Globally x -> collectLiterals x
  Finally x -> collectLiterals x
  Weak x y -> collectLiterals x ++ collectLiterals y
  Not x -> collectLiterals x
  TTrue -> []
  FFalse -> []
  Update {} -> []
  Previous x -> collectLiterals x
  Historically x -> collectLiterals x
  Once x -> collectLiterals x
  Since x y -> collectLiterals x ++ collectLiterals y
  Triggered x y -> collectLiterals x ++ collectLiterals y
  Implies x y -> collectLiterals x ++ collectLiterals y
  Equiv x y -> collectLiterals x ++ collectLiterals y

collectPostconditions :: Formula a -> [(Sygus.Temporal, Literal a)]
collectPostconditions = go []
  where
    go ctx = \case
      Check p -> postconds (Pos p) ctx
      Not (Check p) -> postconds (Neg p) ctx
      And xs -> concatMap (go (BoolFrame : ctx)) xs
      Or xs -> concatMap (go (BoolFrame : ctx)) xs
      Not x -> go (BoolFrame : ctx) x
      Next x -> go (NextFrame : ctx) x
      Until l r -> go (UntilLeft : ctx) l ++ go (UntilRight : ctx) r
      Release l r -> go (ReleaseLeft : ctx) l ++ go (ReleaseRight : ctx) r
      Globally x -> go (BoolFrame : ctx) x
      Finally x -> go (BoolFrame : ctx) x
      Weak l r -> go (BoolFrame : ctx) l ++ go (BoolFrame : ctx) r
      TTrue -> []
      FFalse -> []
      Update {} -> []
      Previous x -> go (BoolFrame : ctx) x
      Historically x -> go (BoolFrame : ctx) x
      Once x -> go (BoolFrame : ctx) x
      Since x y -> go (BoolFrame : ctx) x ++ go (BoolFrame : ctx) y
      Triggered x y -> go (BoolFrame : ctx) x ++ go (BoolFrame : ctx) y
      Implies x y -> go (BoolFrame : ctx) x ++ go (BoolFrame : ctx) y
      Equiv x y -> go (BoolFrame : ctx) x ++ go (BoolFrame : ctx) y

postconds :: Literal a -> [Frame] -> [(Sygus.Temporal, Literal a)]
postconds lit = go 0 []
  where
    go _ acc [] = acc
    go numNext acc (frame : rest) =
      case frame of
        BoolFrame -> go numNext acc rest
        NextFrame ->
          let nextDepth = numNext + 1
           in go nextDepth (acc ++ [(Sygus.Next nextDepth, lit)]) rest
        UntilLeft -> acc ++ [(Sygus.Next 1, lit)]
        UntilRight -> acc ++ [(Sygus.Eventually, lit)]
        ReleaseLeft -> acc ++ [(Sygus.Eventually, lit)]
        ReleaseRight -> acc ++ [(Sygus.Next 1, lit)]

literalToTheory ::
  Theory ->
  (Id -> Int) ->
  (Id -> String) ->
  Literal Id ->
  Either Error TheoryPredicate
literalToTheory theory arityFn unhash = \case
  Pos p ->
    PLiteral
      <$> applySemantics theory (fmap unhash (fromPredicateTerm arityFn p))
  Neg p ->
    NotPLit
      . PLiteral
      <$> applySemantics theory (fmap unhash (fromPredicateTerm arityFn p))

postToTheory ::
  Theory ->
  (Id -> Int) ->
  (Id -> String) ->
  (Sygus.Temporal, Literal Id) ->
  Either Error (Sygus.Temporal, TheoryPredicate)
postToTheory theory arityFn unhash (temporal, lit) =
  (\p -> (temporal, p)) <$> literalToTheory theory arityFn unhash lit

andPredsOrTrue :: Theory -> [TheoryPredicate] -> TheoryPredicate
andPredsOrTrue theory = \case
  [] -> PTrue theory
  [x] -> x
  (x : xs) -> AndPLit x (andPredsOrTrue theory xs)

combinePostconds ::
  Theory ->
  [(Sygus.Temporal, TheoryPredicate)] ->
  (Sygus.Temporal, TheoryPredicate)
combinePostconds theory = \case
  [] -> (Sygus.Next 0, PTrue theory)
  xs ->
    let temporal =
          if any (\(t, _) -> t == Sygus.Eventually) xs
            then Sygus.Eventually
            else Sygus.Next $ maximum $ map nextDepth xs
        preds = map snd xs
     in (temporal, andPredsOrTrue theory preds)
  where
    nextDepth (Sygus.Next n, _) = n
    nextDepth (Sygus.Eventually, _) = 0

powerset :: [a] -> [[a]]
powerset = filterM (const [True, False])
