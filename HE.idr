module HE

import SLanguage
import Algebra

-- This is the "classic" homeomorphic imbedding relation.

mutual

  export
  embeddedIn : Exp -> Exp -> Bool
  embeddedIn e1 e2 = byDiving e1 e2 || byCoupling e1 e2

  byDiving : Exp -> Exp -> Bool
  byDiving e1 (Var _) = False
  byDiving e1 (Call _ _ args) = any (embeddedIn e1) args

  byCoupling : Exp -> Exp -> Bool
  byCoupling (Var _) (Var _) = True
  byCoupling (Call kind1 name1 args1) (Call kind2 name2 args2) =
    kind1 == kind2 && name1 == name2 &&
      and (List.zipWith (\e1,e2 => Delay (embeddedIn e1 e2)) args1 args2)
  byCoupling _ _ = False
