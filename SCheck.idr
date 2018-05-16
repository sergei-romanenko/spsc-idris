module SCheck

import Data.SortedMap
import Data.SortedSet
import Control.Monad.State

import SLanguage

%default total

-- A name belongs to one and only one of the sets:
--   gNames, fNames, pNames, cNames.
-- A variable in a pattern can appear only once.
-- All constructors in the definition of a g-function must be different.
-- A variable appearing in the right hand side must be a parameter.
-- A function name appearing in the right hand side must have a definition.
-- The arities of constructors and functions must be consistent.

Msg : Type
Msg = String

-- Collecting variable names.

vExp : Exp -> List Name
vExp (Var name) = [ name ]
vExp (Call _ _ args) = concatMap (assert_total vExp) args
vExp (Let x xs) = idris_crash "vExp"

-- Repeated names.

repeatedName : List Name -> Maybe Name
repeatedName [] = Nothing
repeatedName (n :: names) =
  if n `elem` names then Just n else repeatedName names

rnFRule : FRule -> Maybe Msg
rnFRule fRule =
  do n <- repeatedName $ rParams fRule
     pure (n ++ " is repeated in the parameters of " ++ rName fRule)

rnGRule : GRule -> Maybe Msg
rnGRule gRule =
  do n <- repeatedName $ rParams gRule
     pure (n ++ " is repeated in the parameters of " ++ rName gRule)

rcGRules : List GRule -> Name -> Maybe Msg
rcGRules gRules name =
  do c <- repeatedName $ [ rcName r | r <- gRules, name == rName r ]
     pure ("In the definition of " ++ name ++ ", " ++
           c ++ " appears twice in the patterns")

-- A variable must be a parameter.

pvFRule : FRule -> Maybe Msg
pvFRule fRule =
  do let ps = fromList $ rParams fRule
     let vs = fromList $ vExp $ rExp fRule
     let [] = SortedSet.toList (vs `difference` ps)
         | (u :: _) =>
              pure ("In the definition of " ++ rName fRule ++ ", " ++
                    u ++ " is not a parameter")
     Nothing

pvGRule : GRule -> Maybe Msg
pvGRule gRule =
  do let ps = fromList $ rParams gRule
     let vs = fromList $ vExp $ rExp gRule
     let [] = SortedSet.toList (vs `difference` ps)
         | (u :: _) =>
             pure ("In the definition of " ++ rName gRule ++ ", " ++
                    u ++ " is not a parameter")
     Nothing

-- Collecting function names.

fExp : Exp -> List Name
fExp (Var name) = []
fExp (Call FC name args) = name :: concatMap (assert_total fExp) args
fExp (Call _ _ args) = concatMap (assert_total fExp) args
fExp (Let x xs) = idris_crash "fExp"

-- We already know that fNames and gNames are disjoint,
-- and all calls to g-functions are marked as GCalls.
-- So, we only need to check that there are rules for FCalls.

uFRule : SortedSet Name -> FRule -> Maybe Msg
uFRule fNames fRule =
  do let fs = fromList $ fExp $ rExp fRule
     let [] = SortedSet.toList (fs `difference` fNames)
         | (f :: _) =>
             pure ("In the definition of " ++ rName fRule ++
                   ", there is a call to an undefined function " ++ f)
     Nothing

uGRule : SortedSet Name -> GRule -> Maybe Msg
uGRule fNames gRule =
  do let fs = fromList $ fExp $ rExp gRule
     let [] = SortedSet.toList (fs `difference` fNames)
         | (f :: _) =>
             pure ("In the definition of " ++ rName gRule ++
                   ", there is a call to an undefined function " ++ f)
     Nothing

uExp : SortedSet Name -> Exp -> Maybe Msg
uExp fNames e =
  do let fs = fromList $ fExp e
     let [] = SortedSet.toList (fs `difference` fNames)
         | (f :: _) =>
             pure ("In the initial expression, " ++
                   "there is a call to an undefined function " ++ f)
     Nothing

-- Arities

ArMap : Type
ArMap = SortedMap Name Nat

updAr : (name : Name) -> (k : Nat) -> State ArMap (Maybe Msg)
updAr name k =
  do arities <- get
     let Just k' = SortedMap.lookup name arities
         | Nothing =>
             do put (insert name k arities)
                pure Nothing
     case k == k' of
       False =>
         pure $ Just (name ++ " has inconsistent arity: " ++
                      show k ++ " and " ++ show k')
       True =>
         pure Nothing

-- Arities of constructors

mutual

  caExp : Exp -> State ArMap (Maybe Msg)
  caExp (Var name) =
    pure Nothing
  caExp (Call Ctr name args) =
    do Nothing <- updAr name (length args)
       | msg => pure msg
       caArgs args
  caExp (Call _ name args) =
    caArgs args
  caExp (Let exp bindings) =
    idris_crash "caExp"

  caArgs : List Exp -> State ArMap (Maybe Msg)
  caArgs [] =
    pure Nothing
  caArgs (arg :: args) =
    do Nothing <- caExp arg
       | msg => pure msg
       caArgs args

caFRules : List FRule -> State ArMap (Maybe Msg)
caFRules [] =
  pure Nothing
caFRules (fRule :: fRules) =
  do Nothing <- caExp $ rExp fRule
     | msg => pure msg
     caFRules fRules

caGRule : GRule -> State ArMap (Maybe Msg)
caGRule (GR rName rcName rcParams rdParams rExp) =
  do Nothing <- updAr rcName (length rcParams)
     | msg => pure msg
     caExp rExp

caGRules : List GRule -> State ArMap (Maybe Msg)
caGRules [] =
  pure Nothing
caGRules (gRule :: gRules) =
  do Nothing <- caGRule gRule
     | msg => pure msg
     caGRules gRules

caTask : Task -> State ArMap (Maybe Msg)
caTask (MkTask e (MkProgram fRules gRules)) =
  do Nothing <- caExp e
     | msg => pure msg
     Nothing <- caFRules fRules
     | msg => pure msg
     Nothing <- caGRules gRules
     | msg => pure msg
     pure Nothing

-- Arities of functions
-- (We already know that fNames and gNames are disjoint.)

mutual

  haExp : Exp -> State ArMap (Maybe Msg)
  haExp (Var name) =
    pure Nothing
  haExp (Call Ctr name args) =
    haArgs args
  haExp (Call _ name args) =
    do Nothing <- updAr name (length args)
       | msg => pure msg
       haArgs args
  haExp (Let exp bindings) =
    idris_crash "haExp"

  haArgs : List Exp -> State ArMap (Maybe Msg)
  haArgs [] =
    pure Nothing
  haArgs (arg :: args) =
    do Nothing <- haExp arg
       | msg => pure msg
       haArgs args

haFRule : FRule -> State ArMap (Maybe Msg)
haFRule (FR rName rParams rExp) =
  do Nothing <- updAr rName (length rParams)
     | msg => pure msg
     haExp rExp

haFRules : List FRule -> State ArMap (Maybe Msg)
haFRules [] =
  pure Nothing
haFRules (fRule :: fRules) =
  do Nothing <- haFRule $ fRule
     | msg => pure msg
     haFRules fRules

haGRule : GRule -> State ArMap (Maybe Msg)
haGRule (GR rName rcName rcParams rdParams rExp) =
  do Nothing <- updAr rName (S $ length rdParams)
     | msg => pure msg
     haExp rExp

haGRules : List GRule -> State ArMap (Maybe Msg)
haGRules [] =
  pure Nothing
haGRules (gRule :: gRules) =
  do Nothing <- haGRule gRule
     | msg => pure msg
     haGRules gRules

haTask : Task -> State ArMap (Maybe Msg)
haTask (MkTask e (MkProgram fRules gRules)) =
  do Nothing <- haExp e
     | msg => pure msg
     Nothing <- haFRules fRules
     | msg => pure msg
     Nothing <- haGRules gRules
     | msg => pure msg
     pure Nothing

export
checkTask : Task -> Maybe String
checkTask task@(MkTask e (MkProgram fRules gRules)) =
  do let fNames = fromList $ map rName fRules
     let gNames = fromList $ map rName gRules
     let hNames = fNames `union` gNames
     let fParams = fromList $ concatMap rParams fRules
     let gParams = fromList $ concatMap rParams gRules
     let pNames = (fromList $ vExp e) `union` (fParams `union` gParams)
     let [] = SortedSet.toList (fNames `intersection` gNames)
         | (name :: _) =>
             Just (name ++ " is both f- and g-function")
     let [] = SortedSet.toList (hNames `intersection` pNames)
         | (name :: _) =>
             Just (name ++ " is both a function and a parameter")
     let Nothing = choiceMap rnFRule fRules
         | msg => msg
     let Nothing = choiceMap rnGRule gRules
         | msg => msg
     let Nothing = choiceMap (rcGRules gRules) gNames
         | msg => msg
     let Nothing = choiceMap pvFRule fRules
         | msg => msg
     let Nothing = choiceMap pvGRule gRules
         | msg => msg
     let Nothing = choiceMap (uFRule fNames) fRules
         | msg => msg
     let Nothing = choiceMap (uGRule fNames) gRules
         | msg => msg
     let Nothing = uExp fNames e
         | msg => msg
     let Nothing = evalState (caTask task) empty
         | msg => msg
     let Nothing = evalState (haTask task) empty
         | msg => msg
     Nothing
