module SParsers

import Text.Token
import Text.Lexer
import Text.Parser

import SLanguage

%default total

--
-- Tokens
--

data IdentKind
  = UId
  | LId

implementation Eq IdentKind where
  (==) UId UId = True
  (==) LId LId = True
  (==) _ _ = False

data SLLTokenKind
  = TkIdent IdentKind
  | TkPunct
  | TkWhere
  | TkIgnore

implementation Eq SLLTokenKind where
  (==) (TkIdent k1) (TkIdent k2) = k1 == k2
  (==) TkPunct TkPunct = True
  (==) TkWhere TkWhere = True
  (==) TkIgnore TkIgnore = True
  (==) _ _ = False

SLLToken : Type
SLLToken = Token SLLTokenKind

TokenKind SLLTokenKind where
  TokType (TkIdent x) = String
  TokType TkPunct = ()
  TokType TkWhere = ()
  TokType TkIgnore = ()

  tokValue (TkIdent k) x = x
  tokValue TkPunct x = ()
  tokValue TkWhere x = ()
  tokValue TkIgnore x = ()

identifier : Lexer
identifier = alpha <+> many alphaNum

uId : Lexer
uId = expect upper <+> identifier

lId : Lexer
lId = expect lower <+> identifier


sllTokenMap : TokenMap SLLToken
sllTokenMap = toTokenMap $
  [ (spaces, TkIgnore)
  , (lineComment (exact "--"), TkIgnore)
  , (exact "where" <+> opt spaces, TkWhere)  
  , (uId, TkIdent UId)
  , (lId, TkIdent LId)
  , (is '(', TkPunct)
  , (is ')', TkPunct)
  , (is ',', TkPunct)
  , (is '=', TkPunct)
  , (is ';', TkPunct)
  ]

lexSLL : String -> Either (Int, Int, String) (List SLLToken)
lexSLL s
  = case lex sllTokenMap s of
         (tokens, _, _, "") => Right $ map TokenData.tok tokens
         (tokens, l, c, rest) => Left (l, c, rest)

--
-- SLL parser
--

uIdent : Grammar SLLToken True Name
uIdent = match (TkIdent UId)

lIdent : Grammar SLLToken True Name
lIdent =  match (TkIdent LId)

symbol : String -> Grammar SLLToken True ()
symbol req = terminal (\t =>
  case t of
    (Tok TkPunct text) => if req == text then Just () else Nothing
    (Tok _ text) => Nothing)

parens : (p : Grammar SLLToken c a) -> Grammar SLLToken True a
parens p = between (symbol "(") (symbol ")") p

commaSep1 : (p : Grammar SLLToken True a) -> Grammar SLLToken True (List a)
commaSep1 p = sepBy1 (symbol ",") p

commaSep : (p : Grammar SLLToken True a) -> Grammar SLLToken False (List a)
commaSep p = sepBy (symbol ",") p

kwWhere : Grammar SLLToken True ()
kwWhere = match TkWhere

--
-- Raw syntax trees
--

mutual

  RArg : Type
  RArg = RExp

  RArgs : Type
  RArgs = List RArg

  RBindings : Type
  RBindings = List (Name, RExp)

  data RExp
    = RVar Name
    | RCtr Name RArgs
    | RCall Name RArgs

data RFRule = RFR Name Params RExp
data RGRule = RGR Name Name Params Params RExp

RRule : Type
RRule = Either RFRule RGRule

data RProgram = MkRProgram (List RRule)

data RTask = MkRTask RExp RProgram

--
-- Programs
--

%default covering

mutual

  expression : Grammar SLLToken True RExp
  expression = constr <|> call <|> variable

  constr : Grammar SLLToken True RExp
  constr =
    do ctrName <- uIdent
       commit
       argList <- option [] (parens (commaSep expression))
       pure $ RCtr ctrName argList

  call : Grammar SLLToken True RExp
  call =
    do name <- lIdent
       argList <- parens (commaSep1 expression)
       pure $ RCall name argList

  variable : Grammar SLLToken True RExp
  variable =
    do name <- lIdent
       pure $ RVar name

fRule : Grammar SLLToken True RRule
fRule =
  do functionName <- lIdent
     paramList <- parens (commaSep1 lIdent)
     commit
     symbol "="
     ruleRhs <- expression
     symbol ";"
     pure $ Left $ RFR functionName paramList ruleRhs

gRule : Grammar SLLToken True RRule
gRule =
  do functionName <- lIdent
     symbol "("
     cname <- uIdent
     commit
     cparamList <- option [] (parens (commaSep lIdent))
     paramList <- many (symbol "," *> lIdent)
     symbol ")"; symbol "="
     ruleRhs <- expression
     symbol ";"
     pure $ Right $ RGR functionName cname cparamList paramList ruleRhs

rule : Grammar SLLToken True RRule
rule = fRule <|> gRule

program : Grammar SLLToken False RProgram
program =
  do ruleList <- many (rule)
     pure $ MkRProgram ruleList

--
-- Supercompilation tasks
--

task : Grammar SLLToken True RTask
task =
  do e <- expression
     kwWhere
     p <- program
     pure $ MkRTask e p


--
-- From the raw abstract syntax to the abstract syntax.
--

startsWithG : String -> Bool
startsWithG name =
  case unpack name of
    [] => False
    (x :: xs) => x == 'g'

toExp : (isGName : Name -> Bool) -> RExp -> Exp
toExp isGName (RVar name) = Var name
toExp isGName (RCtr name args) =
  Call Ctr name (map (toExp isGName) args)
toExp isGName (RCall name args) =
  Call (if isGName name then GC else FC)
        name (map (toExp isGName) args)

toFRule : (isGName : Name -> Bool) -> RFRule -> FRule
toFRule isGName (RFR name params e) =
  FR name params (toExp isGName e)

toGRule : (isGName : Name -> Bool) -> RGRule -> GRule
toGRule isGName (RGR name cname cparams params e) =
  GR name cname cparams params (toExp isGName e)

toRule : (isGName : Name -> Bool) -> RRule -> Rule
toRule isGName = either (Left . toFRule isGName) (Right . toGRule isGName)

toProgram : (isGName : Name -> Bool) -> RProgram -> Program
toProgram isGName (MkRProgram rules) =
  let (fRules, gRules) = partitionEithers rules in
  MkProgram (map (toFRule isGName) fRules) (map (toGRule isGName) gRules)

-- Separating f-functions from g-functions.

getGNames : List RRule -> List Name
getGNames = map (\(RGR name _ _ _ _) => name) . rights

isGNameInProg : RProgram -> Name -> Bool
isGNameInProg (MkRProgram rules) =
  let gNames = getGNames rules in flip elem gNames

toTask : RTask -> Task
toTask (MkRTask e p) =
  let isG = isGNameInProg p in
  MkTask (toExp isG e) (toProgram isG p)

-- Parser

ignored : SLLToken -> Bool
ignored (Tok TkIgnore _) = True
ignored _ = False

getTokenText : List SLLToken -> String
getTokenText [] = "eof"
getTokenText (tk :: tks) = text tk

parseStr : Grammar SLLToken c ast -> String -> Either String ast
parseStr g input =
  case lexSLL input of
    Right toks =>
      case parse g $ filter (not . ignored) toks of
        Right (j, []) => Right j
        Right (j , tk :: _) =>
          Left ("Parsing error: unexpected token " ++ text tk ++ ".")
        Left (Error msg tks) =>
           Left ("Parsing error: " ++ msg ++ ", token " ++ getTokenText tks)
    Left (l, c, rest) =>
      Left ("Lexing error (line " ++ cast l ++ ", column " ++ cast c ++ "): "
                    ++ rest)

export
parseExp : String -> Maybe Exp
parseExp input =
  case parseStr expression input of
    Right e => Just $ toExp startsWithG e
    Left msg => Nothing

export
parseProg : String -> Maybe Program
parseProg input =
  case parseStr program input of
    Right p => Just $ toProgram startsWithG p
    Left msg => Nothing

export
parseTask : String -> Either String Task
parseTask input = toTask <$> parseStr task input
