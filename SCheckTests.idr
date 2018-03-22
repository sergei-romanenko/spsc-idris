module SCheckTests

import Test.Unit

import SLanguage
import SCheck

chTaskOK : Task -> IO Bool
chTaskOK task = assertEquals (checkTask task) Nothing

chTask : Task -> String -> IO Bool
chTask task msg = assertEquals (checkTask task) (Just msg)

testSepFG : IO Bool
testSepFG = chTaskOK (MkTask (Var "a") $ MkProgram
  [ FRule "f" ["x"] (Var "x") ]
  [ GRule "g" "C" [] [] (Call Ctr "C" []) ])

testBothFG : IO Bool
testBothFG = chTask (MkTask (Var "a") $MkProgram
  [ FRule "f" ["x"] (Var "x") ]
  [ GRule "f" "C" [] [] (Call Ctr "C" []) ])
  "f is both f- and g-function"

testBothFGV : IO Bool
testBothFGV = chTask (MkTask (Var "f") $MkProgram
  [ FRule "f" ["x"] (Var "x") ] [])
  "f is both a function and a variable"

testRepFP : IO Bool
testRepFP = chTask (MkTask (Var "a") $ MkProgram
  [ FRule "f" ["x", "x"] (Var "x") ] [])
  "x is repeated in the parameters of f"

testRepGP : IO Bool
testRepGP = chTask (MkTask (Var "a") $ MkProgram
  [] [ GRule "g" "C" ["x"] ["x"] (Var "x") ])
  "x is repeated in the parameters of g"

export
allTests : IO ()
allTests = runTests
  [ testSepFG
  , testBothFG
  , testBothFGV
  , testRepFP
  , testRepGP
  ]
