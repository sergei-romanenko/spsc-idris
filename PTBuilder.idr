module PTBuilder

import Data.SortedMap
import Data.SortedSet
import Control.Monad.State

import SLanguage
import SParsers
import Algebra
import MSG
import HE
import ProcessTree

-- Looking up

lookupF : Program -> Name -> (Params, Exp)
lookupF (MkProgram fRules gRules) name =
  let Just r = find ((name ==) . rName) fRules
      | Nothing => idris_crash "lookupF"
  in (rParams r, rExp r)

lookupGC : Program -> Name -> Name -> (Params, Params, Exp)
lookupGC (MkProgram fRules gRules) name cname =
  let Just r = find (\gr => name == rName gr && cname == rcName gr) gRules
      | Nothing => idris_crash "lookupGC"
  in (rcParams r, rdParams r, rExp r)

lookupG : Program -> Name -> List (Name, Params, Params, Exp)
lookupG (MkProgram fRules gRules) name =
  [ (cname, cparams, params, body) |
    GR name' cname cparams params body <- gRules,
    name == name' ]

-- Driving

applyContr : Maybe Contraction -> Exp -> Exp
applyContr Nothing e = e
applyContr (Just (MkContraction vname cname cparams)) e =
  let cargs = map Var cparams
      vname2ctr = insert vname (Call Ctr cname cargs) empty
  in applySubst vname2ctr e

mutual

  export
  drivingStep : Program -> Exp -> State NameGen (List Branch)
  drivingStep prog e =
    case e of
      Call Ctr name args =>
        pure $ [ (arg, Nothing) | arg <- args  ]
      Call FC name args =>
        let (params, body) = lookupF prog name
            p2a = the Subst $ fromList (params `zip` args)
            body' = applySubst p2a body
        in pure $ [(body', Nothing)]
      Call GC name (Call Ctr cname cargs :: args) =>
        let (cparams, params, body) = lookupGC prog name cname
            pa = (cparams `zip` cargs) ++ (params `zip` args)
            subst = the Subst $ fromList pa
            body' = applySubst subst body
        in pure $ [(body', Nothing)]
      Call GC name (Var vname :: args) =>
        for (lookupG prog name) (\(cname, cparams, params, _) =>
                 driveBranch prog e vname cname cparams params)
      Call GC name (arg0 :: args) =>
        do branches <- drivingStep prog arg0
           pure $ [ (Call GC name (e' :: (map (applyContr c) args)), c)
                    | (e', c) <- branches]
      _ => idris_crash "drivingStep: unexpected case"

  driveBranch : Program -> Exp -> Name -> Name -> Params -> Params ->
                State NameGen Branch
  driveBranch prog e vname cname cparams params =
    do cparams' <- freshNameList (length cparams)
       let cargs = map Var cparams'
       let c = Just $ MkContraction vname cname cparams'
       [(e', Nothing)] <- drivingStep prog (applyContr c e)
       pure $ (e', c)

---- The parts common to the basic and advanced tree builders.

isMoreGeneral : Node -> Node -> Bool
isMoreGeneral beta alpha =
  let eB = nodeExp beta
      eA = nodeExp alpha
  in isFGCall eA && (eB `instOf` eA)

findAMoreGeneralAncestor : Tree -> Node -> Maybe Node
findAMoreGeneralAncestor tree beta =
  if aVarIsUnderAttack (nodeExp beta)
  then findGlobalAncestor (isMoreGeneral beta) tree beta
  else findLocalAncestor (isMoreGeneral beta) tree beta

export
findAnUnprocessedNode : Tree -> Maybe Node
findAnUnprocessedNode tree =
  let leaves = map (getNode tree) (treeLeaves tree) in
  let nodes = [ leaf | leaf <- leaves, not $ isProcessed tree leaf ] in
  case nodes of
    [] => Nothing
    alpha :: _ => Just alpha

public export
BuildStep : Type
BuildStep = Program -> Tree -> Node -> State NameGen Tree

public export
BuildLoop : Type
BuildLoop = BuildStep -> Program -> Tree -> State NameGen Tree

public export
TreeBuilder : Type
TreeBuilder = Program -> Exp -> Tree

buildLoop : BuildLoop
buildLoop buildStep prog tree =
  case findAnUnprocessedNode tree of
    Nothing => pure tree
    Just beta =>
      do tree' <- buildStep prog tree beta
         buildLoop buildStep prog tree'

initTree : Exp -> Tree
initTree e = insert 0 (MkNode 0 e Nothing Nothing [] Nothing) empty

export
mkTreeBuilder : BuildLoop -> BuildStep -> TreeBuilder
mkTreeBuilder loop step prog e =
  let reserved = taskNames(MkTask e prog) in
  (evalState $ loop step prog (initTree e)) (1, reserved, 1)

-- This function replaces the expression in a node with
-- a let-expression, and then adds childe nodes.
-- Thus, a let-node cannot be a leaf.

decomposeNode : Tree -> NodeId -> Exp -> Bindings -> State NameGen Tree
decomposeNode tree nId e bindings =
  do let branches = (e, Nothing) ::
           [ (exp, Nothing) | (name, exp) <- bindings ]
     let tree' = replaceSubtree tree nId (Let e bindings)
     addChildren tree' nId branches

-- If beta `instOf` alpha, we generalize beta by introducing
-- a let-expression, in order to make beta the same as alpha
-- (modulo variable names).

generalizeNode : Program -> Tree -> Node -> Node -> State NameGen Tree
generalizeNode prog tree beta@(MkNode bId eB _ _ _ _)
                         alpha@(MkNode _ eA _ _ _ _) =
  do let Just subst = matchAgainst eA eB
     let bindings = toList subst
     decomposeNode tree bId eA bindings

-- This function applies a driving step to the node's expression,
-- and, in general, adds children to the node.

driveNode : Program -> Tree -> Node -> State NameGen Tree
driveNode prog tree beta@(MkNode bId eB _ _ _ _) =
  do branches <- drivingStep prog eB
     addChildren tree bId branches

---- Basic tree builder

export
basicBuildStep : BuildStep
basicBuildStep prog tree beta =
  case findFuncAncestor tree beta of
    Just alpha =>
      pure $ setBack tree beta (nodeId alpha)
    Nothing =>
      case findAMoreGeneralAncestor tree beta of
        Just alpha => generalizeNode prog tree beta alpha
        Nothing => driveNode prog tree beta

export
basicBuilder : TreeBuilder
basicBuilder prog e =
  mkTreeBuilder buildLoop basicBuildStep prog e

---- Advanced tree builder with homeomorphic imbedding and generalization

abstract : Tree -> Node -> Exp -> Subst -> State NameGen Tree
abstract tree alpha@(MkNode aId eA _ _ _ _) e subst =
  decomposeNode tree aId e (toList subst)

split : Tree -> Node -> State NameGen Tree
split tree b@(MkNode nId e@(Call kind name args) c p chIds back) =
  do names' <- freshNameList (length args)
     let e = Call kind name (map Var names')
     let bindings = names' `zip` args
     decomposeNode tree nId e bindings

generalizeAlphaOrSplit : Tree -> Node -> Node -> State NameGen Tree
generalizeAlphaOrSplit tree beta@(MkNode _ eB _ _ _ _)
                            alpha@(MkNode _ eA _ _ _ _) =
  do MkGen e aSubst bSubst <- msg eA eB
     case e of
       Var _ => split tree beta
       _     => abstract tree alpha e aSubst

isEmbeddedAncestor : Node -> Node -> Bool
isEmbeddedAncestor beta alpha =
  let eB = nodeExp beta
      eA = nodeExp alpha
  in isFGCall eA && (eA `embeddedIn` eB)

findAnEmbeddedAncestor : Tree -> Node -> Maybe Node
findAnEmbeddedAncestor tree beta =
  if aVarIsUnderAttack (nodeExp beta)
  then findGlobalAncestor (isEmbeddedAncestor beta) tree beta
  else findLocalAncestor (isEmbeddedAncestor beta) tree beta

export
advancedBuildStep : BuildStep
advancedBuildStep prog tree beta =
  case findFuncAncestor tree beta of
    Just alpha =>
      pure $ setBack tree beta (nodeId alpha)
    Nothing =>
      case findAMoreGeneralAncestor tree beta of
        Just alpha => generalizeNode prog tree beta alpha
        Nothing =>
          case findAnEmbeddedAncestor tree beta of
            Just alpha => generalizeAlphaOrSplit tree beta alpha
            Nothing => driveNode prog tree beta

export
advancedBuilder : TreeBuilder
advancedBuilder prog e =
  mkTreeBuilder buildLoop advancedBuildStep prog e
