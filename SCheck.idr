module SCheck

import Data.SortedMap
import Data.SortedSet
import Control.Monad.State

import SLanguage

%default total

-- A name belongs to one and only one of the sets:
--   gNames, fNames, vNames, cNames.
-- The arity of constructors and functions must be consistent.
-- All constructors in the definition of a g-function must be different.
-- A variable in a pattern can appear only once.
-- A function name appearing in the right hand side must have a definition.
-- A variable appearing in the right hand side must appear in the left hand side.

-- Collecting variable names.

vExp : Exp -> List Name
vExp (Var name) = [ name ]
vExp (Call _ _ args) = concatMap (assert_total vExp) args
vExp (Let x xs) = idris_crash "vExp"

vFRules : List FRuleT -> List Name
vFRules fRules = concat [ params ++ vExp exp |
  FRule name params exp <- fRules ]

vGRules : List GRuleT -> List Name
vGRules gRules = concat [ cparams ++ params ++ vExp exp |
  GRule name cname cparams params exp <- gRules ]

vProgram : Program -> List Name
vProgram (MkProgram fRules gRules) =
  vFRules fRules ++ vGRules gRules

-- Collecting constructor names.

cExp : Exp -> List Name
cExp (Var name) = []
cExp (Call Ctr name args) = name :: (concatMap (assert_total cExp) args)
cExp (Call _ _ args) = concatMap (assert_total cExp) args
cExp (Let x xs) = idris_crash "cExp"

cFRules : List FRuleT -> List Name
cFRules fRules = concat [ cExp exp | FRule name params exp <- fRules ]

cGRules : List GRuleT -> List Name
cGRules gRules = concat [ cname :: cExp exp |
  GRule name cname cparams params exp <- gRules ]

-- Repeated names.

repeatedName : List Name -> Maybe Name
repeatedName [] = Nothing
repeatedName (n :: names) =
  if n `elem` names then Just n else repeatedName names

rnFRule : FRuleT -> Maybe String
rnFRule fRule =
  do n <- repeatedName $ rParams fRule
     pure (n ++ " is repeated in the parameters of " ++ rName fRule)

rnGRule : GRuleT -> Maybe String
rnGRule gRule =
  do n <- repeatedName $ (rParams gRule ++ rcParams gRule)
     pure (n ++ " is repeated in the parameters of " ++ rName gRule)

{-
shNames : List String -> String
shNames [] = ""
shNames (name :: names) =
  foldl (\ns, n => ns ++ ", " ++ n) name names
-}

export
checkTask : Task -> Maybe String
checkTask (MkTask e (MkProgram fRules gRules)) =
  do let fNames = fromList $ map rName fRules
     let gNames = fromList $ map rName gRules
     let fgNames = fNames `union` gNames
     let vNames = fromList $ vExp e ++ vFRules fRules ++ vGRules gRules
     {-let cNames = fromList $ cExp e ++ cFRules fRules ++ cGRules gRules-}
     let [] = SortedSet.toList (fNames `intersection` gNames)
         | (name :: _) =>
             Just (name ++ " is both f- and g-function")
     let [] = SortedSet.toList (fgNames `intersection` vNames)
         | (name :: _) =>
             Just (name ++ " is both a function and a variable")
     let Nothing = choiceMap rnFRule fRules
         | msg => msg
     let Nothing = choiceMap rnGRule gRules
         | msg => msg
     Nothing
