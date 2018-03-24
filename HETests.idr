module HETests

import Test.Unit

import SLanguage
import SParsers
import HE

--

heTrue : String -> String -> IO Bool
heTrue a1 a2 =
  assertEquals (embeddedIn <$> parseExp a1 <*> parseExp a2) (Just True)

heFalse : String -> String -> IO Bool
heFalse a1 a2 =
  assertEquals (embeddedIn <$> parseExp a1 <*> parseExp a2) (Just False)

heVV : IO Bool
heVV = heTrue "v1" "v2"

heVF : IO Bool
heVF = heTrue "v1" "f(v2)"

heFV : IO Bool
heFV = heFalse "f(v2)" "v1"

heDiving : IO Bool
heDiving = heTrue "f(v1)" "g(v0, f(H(v2)))"

heCoupling1 : IO Bool
heCoupling1 = heTrue "f(v1, g(v2))" "f(H(w1), g(w2))"

heCoupling2 : IO Bool
heCoupling2 = heFalse "f(v1)" "g(w1)"

export
allTests : IO ()
allTests = runTests
  [ heVV
  , heVF
  , heFV
  , heDiving
  , heCoupling1
  , heCoupling2
  ]
