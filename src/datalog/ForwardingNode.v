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
      fnode_pending : list (dfact * node_id);
    }.

  Variant fnode_label :=
    | deduce_label (_ : dfact_mod_count)
    | forward_label (_ : dfact).

  Inductive fnode_step (fp : fnode_prog) (self : node_id) :
    fnode_state -> IO_event fnode_label (dfact * node_id) -> fnode_state -> Prop :=
  | fnode_input fs m :
    fnode_step _ _ fs (I_event m)
               {| fnode_node := fs.(fnode_node); fnode_pending := m :: fs.(fnode_pending) |}
  | fnode_deduce fs ns' lbl outs :
    node_step fp.(fnode_rules) fs.(fnode_node) (O_event lbl outs) ns' ->
    fnode_step _ _ fs (O_event (deduce_label lbl) [])
               {| fnode_node := ns';
                  fnode_pending := map (fun f => (f, self)) outs ++ fs.(fnode_pending) |}
  | fnode_dequeue fs ns' q1 q2 f orig :
    fs.(fnode_pending) = q1 ++ (f, orig) :: q2 ->
    (if fp.(fnode_keep) (dfact_rel f)
     then node_step fp.(fnode_rules) fs.(fnode_node) (I_event f) ns'
     else ns' = fs.(fnode_node)) ->
    fnode_step _ _ fs (O_event (forward_label f) [(f, orig)])
               {| fnode_node := ns'; fnode_pending := q1 ++ q2 |}.

  Context (input_allowed : node_id -> dfact -> bool).
  Context (output_visible : node_id -> dfact -> bool).
  Context (fforward : node_id -> node_id -> (dfact * node_id) -> bool).
  Context (nforward : node_id -> node_id -> dfact -> bool).
  Context (fprog_at : node_id -> fnode_prog).
  Context {fgraph_state : map.map node_id (graph_node_state (dfact * node_id) fnode_label fnode_state)}.
  Context {ngraph_state : map.map node_id (graph_node_state dfact dfact_mod_count node_state)}.

  Definition finput_allowed n (m : dfact * node_id) := let '(f, _) := m in input_allowed n f.

  Definition foutput_visible n (m : dfact * node_id) := let '(f, _) := m in output_visible n f.

  Definition fgraph_step :=
    graph_step finput_allowed fforward foutput_visible
      (fun n => fnode_step (fprog_at n) n).

  Definition ngraph_step :=
    graph_step input_allowed nforward output_visible
      (fun n => node_step (fprog_at n).(fnode_rules)).
End __.
