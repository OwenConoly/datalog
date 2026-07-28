From Stdlib Require Import List Lia Permutation Classical_Prop RelationClasses.
From Datalog Require Import List Datalog Smallstep Tactics Graph Node.
From coqutil Require Import Map.Interface.
From coqutil Require Import Semantics.OmniSmallstepCombinators Tactics Tactics.fwd.
Import ListNotations.

Section __.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context {sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Context {node_prog node_state : Type}.
  Context (node_step : node_prog -> node_state -> IO_event dfact_mod_count dfact -> node_state -> Prop).

  Record fnode_prog :=
    { fnode_rules : node_prog;
      fnode_keep : rel -> bool
    }.

  Record fnode_state :=
    { fnode_node : node_state;
      fnode_pending : list dfact;
    }.

  Variant fnode_label :=
    | deduce_label (_ : dfact_mod_count)
    | forward_label (_ : dfact).

  Context (fp : fnode_prog).

  Inductive fnode_step : fnode_state -> IO_event fnode_label dfact -> fnode_state -> Prop :=
  | fnode_input fs f :
    fnode_step fs (I_event f)
               {| fnode_node := fs.(fnode_node); fnode_pending := f :: fs.(fnode_pending) |}
  | fnode_deduce fs ns' lbl outs :
    node_step fp.(fnode_rules) fs.(fnode_node) (O_event lbl outs) ns' ->
    fnode_step fs (O_event (deduce_label lbl) [])
               {| fnode_node := ns'; fnode_pending := outs ++ fs.(fnode_pending) |}
  | fnode_dequeue fs ns' q1 q2 f :
    fs.(fnode_pending) = q1 ++ f :: q2 ->
    (if fp.(fnode_keep) (dfact_rel f)
     then node_step fp.(fnode_rules) fs.(fnode_node) (I_event f) ns'
     else ns' = fs.(fnode_node)) ->
    fnode_step fs (O_event (forward_label f) [f])
               {| fnode_node := ns'; fnode_pending := q1 ++ q2 |}.
End __.
