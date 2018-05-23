module ResProgGen

import Data.SortedMap
import Control.Monad.State

import Algebra
import SLanguage
import ProcessTree

--

partial
hd : List a -> a
hd [] = idris_crash "hd"
hd (x :: xs) = x

partial
tl : List a -> List a
tl [] = idris_crash "tl"
tl (x :: xs) = xs

--

Sig : Type
Sig = (Name, List Name)

Sigs : Type
Sigs = SortedMap Nat Sig

SigsRules : Type
SigsRules = (Sigs, List FRule, List GRule)

isVarTest : Tree -> Node -> Bool
isVarTest tree (b@(MkNode _ _ _ _ (bChId :: _) _)) =
  isJust $ nodeContr $ getNode tree bChId

isFuncNode : List NodeId -> NodeId -> Bool
isFuncNode fIds nId = nId `elem` fIds

getFGSig : Tree -> NodeId -> Name -> List Name ->
           State SigsRules Sig
getFGSig tree nId name vs =
  do (sigs, fRules, gRules) <- get
     case the (Maybe Sig) $ lookup nId sigs of
       Nothing =>
         do let name' = name ++ (show $ S (length $ toList sigs))
            let sig' = (name', vs)
            let sigs' = insert nId sig' sigs
            put $ (sigs', fRules, gRules)
            pure sig'
       Just sig' =>
         pure sig'

putFRules : List FRule -> State SigsRules ()
putFRules newRules =
  do (sigs, fRules, gRules) <- get
     let fRules' = fRules ++ newRules
     put (sigs, fRules', gRules)

putGRules : List GRule -> State SigsRules ()
putGRules newRules =
  do (sigs, fRules, gRules) <- get
     let gRules' = gRules ++ newRules
     put (sigs, fRules, gRules')

getChContr : Tree -> List NodeId -> List (Name, List Name)
getChContr tree nIds =
  let children = map (getNode tree) nIds in
  [ (cname, cparams)  |
    MkNode _ _ (Just (MkContraction _ cname cparams)) _ _ _ <- children]

mutual

  genResExp : Tree -> List NodeId -> Node -> State SigsRules Exp
  genResExp tree fIds b@(MkNode _ bE _ _ bChIds Nothing) =
    case bE of
      Var _ => pure $ bE
      Call Ctr cname _ =>
        do es <- genResExps tree fIds bChIds
           pure $ Call Ctr cname es
      Call FC name args =>
        genResCall tree fIds b name args
      Call GC name args =>
        genResCall tree fIds b name args
      Let _ bs =>
        do let chNode = getNode tree (hd bChIds)
           e' <- genResExp tree fIds chNode
           es' <- genResExps tree fIds (tl bChIds)
           let vnames = map fst bs
           let subst = fromList (vnames `zip` es')
           pure $ applySubst subst e'
  genResExp tree fIds b@(MkNode _ bE _ _ bChIds (Just aId)) =
    do let MkNode _ aE aC _ (aChId :: _) _ = getNode tree aId
       (sigs, rules) <- get
       let Just (name, params) = lookup aId sigs
       let args = map Var params
       let Just subst = matchAgainst aE bE
       let aChNode = getNode tree aChId
       case nodeContr aChNode of
         Nothing =>
           pure $ applySubst subst (Call FC name args)
         Just _ =>
           pure $ applySubst subst (Call GC name args)

  genResExps : Tree -> List NodeId -> List NodeId ->
                    State SigsRules (List Exp)
  genResExps tree fIds nIds =
    for (map (getNode tree) nIds) (genResExp tree fIds)

  genResCall : Tree -> List NodeId -> Node -> Name -> List Exp ->
                    State SigsRules Exp
  genResCall tree fIds (b@(MkNode bId bE _ _ bChIds _)) name args =
    let params = vars bE in
    if isVarTest tree b then
      do (sigs, rules) <- get
         (name', _) <- getFGSig tree bId name params
         bodies <- genResExps tree fIds bChIds
         let contrs = getChContr tree bChIds
         let gRules =
               [ GR name' cname' cparams' (tl params) body' |
                  ((cname', cparams'), body') <- contrs `zip` bodies]
         putGRules gRules
         pure $ Call GC name' (map Var params)
    else if isFuncNode fIds bId then
      do (sigs, rules) <- get
         (name', params') <- getFGSig tree bId name params
         let bChNode = getNode tree (hd bChIds)
         body' <- genResExp tree fIds bChNode
         putFRules [ FR name' params' body']
         pure $ Call FC name' (map Var params)
    else
      let bChNode = getNode tree (hd bChIds) in
      genResExp tree fIds bChNode

genResidualProgram' : Tree -> State SigsRules (Exp, Program)
genResidualProgram' tree =
  do let initNode = getNode tree 0
     let fIds = funcNodeIds tree
     resExp <- genResExp tree fIds initNode
     (_, fRules, gRules) <- get
     pure (resExp, MkProgram fRules gRules)

export
genResidualProgram : Tree -> (Exp, Program)
genResidualProgram tree =
  (evalState $ genResidualProgram' tree) (empty, [], [])
