-- | Tests for NNF conversion.
module LogicNNFTests
  ( tests,
  )
where

import Distribution.TestSuite
  ( Progress (..),
    Result (..),
    Test (..),
    TestInstance (..),
  )
import TSL.Base.Logic
  ( Formula (..),
    PredicateTerm (..),
    toNNF,
  )
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
makeTestName = ("NNF >> " ++)

tests :: IO [Test]
tests = do
  let p = PredicateSymbol "p"
      q = PredicateSymbol "q"
      cp = Check p
      cq = Check q
      cases =
        [ ("Globally", toNNF (Globally cp), Just $ Release FFalse cp),
          ("Not Finally", toNNF (Not (Finally cp)), Just $ Release FFalse (Not cp)),
          ("Not Until", toNNF (Not (Until cp cq)), Just $ Release (Not cp) (Not cq)),
          ("Weak", toNNF (Weak cp cq), Just $ Or [Until cp cq, Release FFalse cp]),
          ("Past", toNNF (Previous cp), Nothing)
        ]
      mkCase (label, actual, expected) =
        return $ H.TestCase $ case expected of
          Just expVal -> case actual of
            Right got -> got @=? expVal
            Left _ -> H.assertFailure ("Unexpected failure in case: " ++ label)
          Nothing -> case actual of
            Left _ -> True @=? True
            Right _ -> H.assertFailure ("Expected failure for past operator: " ++ label)

  tests' <- mapM mkCase cases
  return [convert2Cabal (makeTestName "NNF") (return $ H.TestList tests')]
