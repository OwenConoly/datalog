From Stdlib Require Import List Lia Permutation Classical_Prop RelationClasses.
From Datalog Require Import List Datalog Smallstep Tactics Graph Map Default Eqb Node.
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

End __.
Arguments fnode_prog : clear implicits.
Arguments fnode_label : clear implicits.
Arguments fnode_state : clear implicits.

Section __.
  Context {rel : relT} {T : valueT}.
  Context {node_prog node_state : Type}.
  Context {label : Type}.
  Context (node_step : node_prog -> node_state -> IO_event label dfact -> node_state -> Prop).
  Context (input_allowed : node_id -> dfact -> bool).
  Context (output_visible : node_id -> dfact -> bool).
  Context (nforward : node_id -> rel -> list node_id).
  Context {forwarding_table : map.map (rel * node_id) (list node_id)}.
  Context {forwarding_tables : map.map node_id forwarding_table}.
  Context {graph : graph.graph node_id}.
  Context (fts : forwarding_tables).
  Context (prog_at : node_id -> node_prog).
  Context {fgraph_state : map.map node_id
            (graph_node_state (dfact * node_id) (fnode_label dfact label) (fnode_state node_state dfact))}.
  Context {ngraph_state : map.map node_id (graph_node_state dfact label node_state)}.

  Definition fprog_at n : fnode_prog node_prog dfact :=
    {| fnode_rules := prog_at n;
       fnode_keep := fun f => existsb (eqb n) (nforward n (dfact_rel f)) |}.

  Definition finput_allowed n (m : dfact * node_id) :=
    let '(f, _) := m in input_allowed n f.

  Definition foutput_visible n (m : dfact * node_id) :=
    let '(f, _) := m in output_visible n f.

  Definition reannotate '(m, n) : dfact * node_id * node_id := (m, n, n).

  Definition fforward (src : node_id) (mn : rel * node_id) : list node_id :=
    get_or_default (get_or_default fts src) mn.

  Definition fgraph_step g1 e g2 :=
    graph_step finput_allowed
      (fun src dst '(f, orig) => existsb (eqb dst) (fforward src (dfact_rel f, orig)))
      foutput_visible
      (fun n => fnode_step node_step (fprog_at n) n)
      g1 (translate_event reannotate e) g2.

  Definition forwarding_graph (mn : rel * node_id) :=
    map.fold (fun g src tbl => graph.put_edges g src (get_or_default tbl mn)) graph.empty fts.

  Definition ngraph_step :=
    graph_step input_allowed
      (fun src dst m => existsb (eqb dst) (nforward src (dfact_rel m))) output_visible
      (fun n => node_step (fprog_at n).(fnode_rules)).

  Definition forwarding_tree :=
    forall R n,
      graph.is_locally_tree (forwarding_graph (R, n)) n.

  Definition forwarding_reaches :=
    forall R n n',
      In n' (nforward n R) ->
      graph.reaches (forwarding_graph (R, n)) n n'.

  Definition can_make_it R orig cur destn :=
    In destn (nforward orig R) /\ graph.reaches (forwarding_graph (R, orig)) cur destn.

  Definition incoming_msgs (fs : fgraph_state) (destn : node_id) : list dfact -> Prop :=
    flat_map_Prop (fun '(cur, ns) =>
                   fun msgs =>
                     exists msgs_lbls,
                       filter_Prop (fun '(f, orig) => can_make_it (dfact_rel f) orig cur destn)
                         (ns.(gns_queue) ++ ns.(gns_node_state).(fnode_pending))
                         msgs_lbls /\
                         msgs = map fst msgs_lbls)
      (map.tuples fs).

  Definition forwarding_R {Lf Ln}
    (s1 : fgraph_state) (t1 : list (IO_event Lf (dfact * node_id)))
    (s2 : ngraph_state) (t2 : list (IO_event Ln (dfact * node_id))) : Prop :=
    flat_map inputs_of t1 = flat_map inputs_of t2 /\
      Forall2_map (fun destn fgns ngns =>
                     fgns.(gns_node_state).(fnode_node) = ngns.(gns_node_state) /\
                       exists msgs,
                         incoming_msgs s1 destn msgs /\
                           Permutation msgs ngns.(gns_queue))
        s1 s2.

  Lemma fgraph_weak_sims_ngraph :
    weak_sim fgraph_step ngraph_step forwarding_R.
  Proof.
  Admitted.
End __.
