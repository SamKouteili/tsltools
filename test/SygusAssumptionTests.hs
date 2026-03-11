-- | Tests for SyGuS assumption formatting.
module SygusAssumptionTests
  ( tests,
  )
where

import Distribution.TestSuite
  ( Progress (..),
    Result (..),
    Test (..),
    TestInstance (..),
  )
import Data.List (isInfixOf)
import TSL.ModuloTheories.Predicates (TheoryPredicate (..))
import TSL.ModuloTheories.Sygus.Assumption (makeAssumption)
import TSL.ModuloTheories.Sygus.Common (Dto (..), Temporal (..))
import TSL.ModuloTheories.Theories (Theory (..))
import Test.HUnit ((@=?))
import qualified Test.HUnit as H

convert2Cabal :: String -> IO H.Test -> Test
convert2Cabal name = Test . testInstance name

testInstance :: String -> IO H.Test -> TestInstance
testInstance name test =
  TestInstance
    { run = runTest test,
      name = name,
      tags = [],
      options = [],
      setOption = \_ _ -> Right $ testInstance name test
    }

runTest :: IO H.Test -> IO Progress
runTest = (fmap snd . H.performTest onStart onError onFailure us =<<)
  where
    onStart :: H.State -> Progress -> IO Progress
    onStart _ = return

    onError :: a -> String -> H.State -> Progress -> IO Progress
    onError _ msg _ _ = return $ Finished (Error $ concatMap (++ " ") (lines msg))

    onFailure :: a -> String -> H.State -> Progress -> IO Progress
    onFailure _ msg _ _ = return $ Finished (Fail $ concatMap (++ " ") (lines msg))

    us :: Progress
    us = Finished Pass

makeTestName :: String -> String
makeTestName = ("SyGuS Assumption >> " ++)

tests :: IO [Test]
tests = do
  let dtoNext =
        Dto
          { theory = Lia,
            preCondition = PTrue Lia,
            postCondition = PTrue Lia,
            temporal = Next 2
          }
      dtoEventually =
        Dto
          { theory = Lia,
            preCondition = PTrue Lia,
            postCondition = PTrue Lia,
            temporal = Eventually
          }

      mkCase label dto expectedSnippet = do
        let result = makeAssumption dto []
        return $
          H.TestCase $ case result of
            Left err -> H.assertFailure $ show err
            Right txt -> H.assertBool ("Missing " ++ expectedSnippet) (expectedSnippet `isInfixOf` txt)

  nextCase <- mkCase "Next" dtoNext "X(X("
  eventualCase <- mkCase "Eventually" dtoEventually "F("

  return [convert2Cabal (makeTestName "Format") (return $ H.TestList [nextCase, eventualCase])]
