module SCheckTests

import Test.Unit

import SLanguage
import SCheck

chTaskOK : Task -> IO Bool
chTaskOK task = assertEquals (checkTask task) Nothing

chTask : Task -> String -> IO Bool
chTask task msg = assertEquals (checkTask task) (Just msg)

testSepFG : IO Bool
testSepFG = chTaskOK $ MkTask (Var "a") $ MkProgram
  [ FR "f" ["x"] (Var "x") ]
  [ GR "g" "C1" [] ["y"] (Call Ctr "C" [])
  , GR "g" "C2" ["x"] ["y"] (Call GC "g" [Var "x", Var "y"]) ]

testBothFG : IO Bool
testBothFG = chTask (MkTask (Var "a") $ MkProgram
  [ FR "f" ["x"] (Var "x") ]
  [ GR "f" "C" [] [] (Call Ctr "C" []) ])
  "f is both f- and g-function"

testBothFGV : IO Bool
testBothFGV = chTask (MkTask (Var "f") $ MkProgram
  [ FR "f" ["x"] (Var "x") ] [])
  "f is both a function and a parameter"

testRepFP : IO Bool
testRepFP = chTask (MkTask (Var "a") $ MkProgram
  [ FR "f" ["x", "x"] (Var "x") ] [])
  "x is repeated in the parameters of f"

testRepGP : IO Bool
testRepGP = chTask (MkTask (Var "a") $ MkProgram
  [] [ GR "g" "C" ["x"] ["x"] (Var "x") ])
  "x is repeated in the parameters of g"

testRepGC : IO Bool
testRepGC = chTask (MkTask (Var "a") $ MkProgram []
  [ GR "g" "C" ["x"] [] (Var "x")
  , GR "g" "C" ["x"] [] (Var "x") ]
  )
  "In the definition of g, C appears twice in the patterns"

testUFPV : IO Bool
testUFPV = chTask (MkTask (Var "a") $ MkProgram
  [ FR "f" ["x"] (Var "y") ] [])
  "In the definition of f, y is not a parameter"

testUGPV : IO Bool
testUGPV = chTask (MkTask (Var "a") $ MkProgram
  [] [ GR "g" "C" ["x"] ["y"] (Var "z") ])
  "In the definition of g, z is not a parameter"

testUFF : IO Bool
testUFF = chTask (MkTask (Var "a") $ MkProgram
  [ FR "f" [] (Call FC "f1" []) ] [])
  "In the definition of f, there is a call to an undefined function f1"

testUGF : IO Bool
testUGF = chTask (MkTask (Var "a") $ MkProgram
  [] [ GR "g" "C" [] [] (Call FC "f1" []) ])
  "In the definition of g, there is a call to an undefined function f1"

testArCF : IO Bool
testArCF = chTask (MkTask (Call Ctr "C" []) $ MkProgram
  [ FR "f" ["x"] (Call Ctr "C" [Var "x"]) ] [])
  "C has inconsistent arity: 1 and 0"

testArCG : IO Bool
testArCG = chTask (MkTask (Var "a") $ MkProgram
  [] [ GR "g" "C" ["x"] [] (Call Ctr "C" []) ])
  "C has inconsistent arity: 0 and 1"

testArHF1 : IO Bool
testArHF1 = chTask (MkTask (Call FC "f" []) $ MkProgram
  [ FR "f" ["x"] (Var "x") ] [])
  "f has inconsistent arity: 1 and 0"

testArHF2 : IO Bool
testArHF2 = chTask (MkTask (Call Ctr "C" [Var "a"]) $ MkProgram
  [ FR "f" ["x"] (Call Ctr "C" [Call FC "f" []]) ] [])
  "f has inconsistent arity: 0 and 1"

testArHG1 : IO Bool
testArHG1 = chTask (MkTask (Var "a") $ MkProgram
  [] [ GR "g" "C" [] [] (Call GC "g" []) ])
  "g has inconsistent arity: 0 and 1"

export
allTests : IO ()
allTests = runTests
  [ testSepFG
  , testBothFG
  , testBothFGV
  , testRepFP
  , testRepGP
  , testRepGC
  , testUFPV
  , testUGPV
  , testUFF
  , testUGF
  , testArCF
  , testArCG
  , testArHF1
  , testArHF2
  , testArHG1
  ]
