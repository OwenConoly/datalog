From Stdlib Require Import List Lia Permutation Classical_Prop RelationClasses.
From Datalog Require Import List Smallstep Tactics Graph Map Default Eqb.
From GraphSearch Require Import GraphInterface.
From coqutil Require Import Map.Interface.
From coqutil Require Import Eqb Semantics.OmniSmallstepCombinators Tactics Tactics.fwd.
Import ListNotations.

Section __.
  Context {node_prog node_state : Type}.
  Context {message label : Type}.
  Context (node_step : node_prog -> node_state -> IO_event label message -> node_state -> Prop).

  Record fnode_prog :=
    { fnode_rules : node_prog;
      fnode_keep : message -> bool
    }.

  Record fnode_state :=
    { fnode_node : node_state;
      fnode_pending : list (message * node_id);
    }.

  Variant fnode_label :=
    | deduce_label (_ : label)
    | forward_label (_ : message).

  Inductive fnode_step (fp : fnode_prog) (self : node_id) :
    fnode_state -> IO_event fnode_label (message * node_id) -> fnode_state -> Prop :=
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
    (if fp.(fnode_keep) f
     then node_step fp.(fnode_rules) fs.(fnode_node) (I_event f) ns'
     else ns' = fs.(fnode_node)) ->
    fnode_step _ _ fs (O_event (forward_label f) [(f, orig)])
               {| fnode_node := ns'; fnode_pending := q1 ++ q2 |}.

  Context (input_allowed : node_id -> message -> bool).
  Context (output_visible : node_id -> message -> bool).
  Context (fforward : node_id -> (message * node_id) -> list node_id).
  Context (nforward : node_id -> message -> list node_id).
  Context {forwarding_table : map.map (message * node_id) (list node_id)}.
  Context {forwarding_tables : map.map node_id forwarding_table}.
  Context {graph : graph.graph node_id}.
  Context (fprog_at : node_id -> fnode_prog).
  Context {fgraph_state : map.map node_id (graph_node_state (message * node_id) fnode_label fnode_state)}.
  Context {ngraph_state : map.map node_id (graph_node_state message label node_state)}.

  Definition finput_allowed n (m : message * node_id) :=
    let '(f, _) := m in input_allowed n f.

  Definition foutput_visible n (m : message * node_id) :=
    let '(f, _) := m in output_visible n f.

  Definition fgraph_step :=
    graph_step finput_allowed
      (fun src dst m => existsb (eqb dst) (fforward src m)) foutput_visible
      (fun n => fnode_step (fprog_at n) n).

  Definition ngraph_step :=
    graph_step input_allowed
      (fun src dst m => existsb (eqb dst) (nforward src m)) output_visible
      (fun n => node_step (fprog_at n).(fnode_rules)).

  Definition forwarding_graph (ft : forwarding_tables) (mn : message * node_id) :=
    map.fold (fun g src tbl => graph.put_edges g src (get_or_default tbl mn)) graph.empty ft.

  Definition forwarding_tree ft :=
    forall m n,
      graph.is_locally_tree (forwarding_graph ft (m, n)) n.

  Definition forwarding_reaches ft :=
    forall m n n',
      In n' (nforward n m) ->
      graph.reaches (forwarding_graph ft (m, n)) n n'.


End __.
