module Algebra

import Data.SortedMap
import Data.SortedSet
import Control.Monad.State

import SLanguage

%default total

%access public export

-- Substitutions

Subst : Type
Subst = SortedMap Name Exp

implementation Eq Subst where
  (==) subst1 subst2 = toList subst1 == toList subst2

theSameFunctor : Exp -> Exp -> Bool
theSameFunctor (Call kind1 name1 _) (Call kind2 name2 _) =
  kind1 == kind2 && name1 == name2
theSameFunctor _ _ = False

applySubst : Subst -> Exp -> Exp
applySubst m e = case e of
  Var name =>
    fromMaybe e (lookup name m)
  Call kind name args =>
    Call kind name (map (assert_total $ applySubst m) args)
  Let e bindings =>
    idris_crash "Algebra.applySubst"

-- Matching

mutual

  matchAgainstAcc : Maybe Subst -> Exp -> Exp -> Maybe Subst
  matchAgainstAcc (Just m) (Var vname) e' =
    case lookup vname m of
      Nothing => Just $ insert vname e' m
      Just e'' =>
        if e' /= e'' then Nothing else Just m
  matchAgainstAcc (Just m) (Call kind name args) (Call kind' name' args') =
    if kind == kind' && name == name'
          then matchAgainstAccL (Just m) args args' else Nothing
  matchAgainstAcc _ _ _ = Nothing

  matchAgainstAccL : Maybe Subst -> Args -> Args -> Maybe Subst
  matchAgainstAccL (Just m) [] [] = (Just m)
  matchAgainstAccL (Just m) (e :: es) (e' :: es') =
    matchAgainstAccL (matchAgainstAcc (Just m) e e') es es'
  matchAgainstAccL _ _ _ = Nothing

matchAgainst : Exp -> Exp -> Maybe Subst
matchAgainst e e' = matchAgainstAcc (Just empty) e e'

instOf : Exp -> Exp -> Bool
instOf e' e =
  case matchAgainst e e' of
    Nothing => False
    Just _ => True

equiv : Exp -> Exp -> Bool
equiv e1 e2 = (e1 `instOf` e2) && (e2 `instOf` e1)

-- Function calls

isFGCall : Exp -> Bool
isFGCall (Call FC _ _) = True
isFGCall (Call GC _ _) = True
isFGCall _ = False

-- Free variables

vars : Exp -> List Name
vars (Var vname) = [vname]
vars (Call _ _ args) =
  foldl union [] (assert_total $ map vars args)
vars (Let e bs) = []

-- Names appearing in the task

expNames : Exp -> SortedSet Name
expNames (Var name) = insert name empty
expNames (Call ckind name args) =
  foldl union (insert name empty) (map (assert_total expNames) args)
expNames (Let e bs) =
  foldl union (expNames e `union` fromList (map fst bs))
              (map (assert_total expNames . snd) bs)

fRuleNames : FRule -> SortedSet Name
fRuleNames (FR name params e) =
  fromList (name :: params) `union` expNames e

gRuleNames : GRule -> SortedSet Name
gRuleNames (GR name cName cParams dParams e) =
  fromList (name :: cName :: cParams ++ dParams) `union` expNames e

total
taskNames : Task -> SortedSet Name
taskNames (MkTask e (MkProgram fRules gRules)) =
  foldl union (expNames e) (map fRuleNames fRules ++ map gRuleNames gRules)

-- Fresh names

NameGen : Type
NameGen = (Nat, SortedSet Name, Nat)

freshName : String -> State NameGen Name
freshName prefix =
  do (fId, ns, k) <- get
     let name = prefix ++ show k
     if contains name ns then
       do put $ (fId, ns, S k)
          assert_total $ freshName prefix
     else
       do put $ (fId, SortedSet.insert name ns, S k)
          pure $ name

freshNameList : Nat -> State NameGen (List Name)
freshNameList n = case n of
  Z => pure $ []
  S n' =>
     do name <- freshName "v"
        nameList <- freshNameList n'
        pure $ name :: nameList
