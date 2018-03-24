module SLanguage

%default total

%access public export

Name : Type
Name = String

Params : Type
Params = List Name

data CKind = Ctr | FC | GC

mutual

  Arg : Type
  Arg = Exp
  
  Args : Type
  Args = List Arg

  Bindings : Type
  Bindings = List (Name, Exp)

  data Exp : Type where
    Var  : (name : Name) -> Exp
    Call : (ckind : CKind) -> (name : Name) -> (args : Args) -> Exp
    Let  : (exp : Exp) -> (bindings : Bindings) -> Exp

record FRule where
  constructor FR
  rName : Name
  rParams : Params
  rExp : Exp

record GRule where
  constructor GR
  rName : Name
  rcName : Name
  rcParams : Params
  rdParams : Params
  rExp : Exp

rParams : GRule -> List Name
rParams gRule = rcParams gRule ++ rdParams gRule

Rule : Type
Rule = Either FRule GRule

data Program = MkProgram (List FRule) (List GRule)

data Task = MkTask Exp Program

--- Show ---

mutual

  showParams : List String -> String
  showParams [] = ""
  showParams (x :: xs) = x ++ showParamsTail xs

  showParamsTail : List String -> String
  showParamsTail [] = ""
  showParamsTail xs@(_ :: _) = "," ++ showParams xs

showPat : String -> List String -> String
showPat cname [] = cname
showPat cname cparams =
  cname ++ "(" ++ showParams cparams ++ ")"

mutual

  showArgs : List Exp -> String

  showArgs [] = "()"
  showArgs (x :: xs) = "(" ++ show x ++ showArgsTail xs ++ ")"

  showArgsTail : List Exp -> String

  showArgsTail [] = ""
  showArgsTail (x :: xs) = "," ++ show x ++ showArgsTail xs

  showBindings : List (String, Exp) -> String

  showBindings [] = ""
  showBindings ((v, e) :: xs) = v ++ "=" ++ show e ++ showBindingsTail xs

  showBindingsTail : List (String, Exp) -> String

  showBindingsTail [] = ""
  showBindingsTail xs@(_ :: _) = "," ++ showBindings xs

  implementation Show Exp where
    show (Var name) = name
    show (Call Ctr name []) = name
    show (Call _ name args) = name ++ showArgs args
    show (Let e bindings) = "let " ++ showBindings bindings ++ " in " ++ show e

implementation Show FRule where
  show (FR name params exp) =
    name ++ "(" ++ showParams params ++ ")=" ++ show exp ++ ";"

implementation Show GRule where
  show (GR name cname cparams params expression) =
    name ++ "(" ++ showPat cname cparams ++ showParamsTail params ++ ")="
        ++ show expression ++ ";"

implementation Show Program where
  show (MkProgram fRules gRules) =
    concatMap show fRules ++ concatMap show gRules

implementation Show Task where
  show (MkTask e prog) = show e ++ " where " ++ show prog

--
-- Eq
--

implementation Eq CKind where
  (==) Ctr Ctr = True
  (==) FC FC = True
  (==) GC GC = True
  (==) _ _ = False

implementation Eq Exp where
  (==) (Var name1) (Var name2) = name1 == name2
  (==) (Call ctr1 name1 args1) (Call ctr2 name2 args2) =
    ctr1 == ctr2 && name1 == name2 && assert_total (args1 == args2)
  (==) (Let e1 bs1) (Let e2 bs2) =
    e1 == e2 && assert_total (bs1 == bs2)
  (==) _ _ = False
