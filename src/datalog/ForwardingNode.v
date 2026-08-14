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
      fnode_pending : list (message * option node_id);
    }.

  Variant fnode_label :=
    | deduce_label (_ : label)
    | forward_label (_ : message).

  Inductive fnode_step (fp : fnode_prog) (self : node_id) :
    fnode_state -> IO_event fnode_label (message * option node_id) -> fnode_state -> Prop :=
  | fnode_input fs m :
    fnode_step _ _ fs (I_event m)
               {| fnode_node := fs.(fnode_node); fnode_pending := m :: fs.(fnode_pending) |}
  | fnode_deduce fs ns' lbl outs :
    node_step fp.(fnode_rules) fs.(fnode_node) (O_event lbl outs) ns' ->
    fnode_step _ _ fs (O_event (deduce_label lbl) [])
               {| fnode_node := ns';
                  fnode_pending := map (fun f => (f, Some self)) outs ++ fs.(fnode_pending) |}
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
  Context (input_locs : rel -> list node_id).
  Context (output_visible : node_id -> dfact -> bool).
  Context (nforward : node_id -> rel -> list node_id).
  Context {forwarding_table : map.map (rel * option node_id) (list node_id)}.
  Context {forwarding_tables : map.map node_id forwarding_table}.
  Context {graph : graph.graph node_id}.
  Context (fts : forwarding_tables).
  Context (prog_at : node_id -> node_prog).
  Context {fgraph_state : map.map node_id
            (graph_node_state (dfact * option node_id) (fnode_label dfact label) (fnode_state node_state dfact))}.
  Context {ngraph_state : map.map node_id (graph_node_state dfact label node_state)}.

  Local Notation flabel := (graph_label (dfact * option node_id) (fnode_label dfact label)).
  Local Notation nlabel := (graph_label dfact label).
  Local Notation IO_event := (Smallstep.IO_event flabel dfact).
  Local Notation fIO_event := (Smallstep.IO_event flabel (dfact * option node_id)).
  Local Notation nIO_event := (Smallstep.IO_event nlabel dfact).

  Definition fprog_at n : fnode_prog node_prog dfact :=
    {| fnode_rules := prog_at n;
       fnode_keep := fun f => existsb (eqb n) (nforward n (dfact_rel f)) |}.

  Definition foutput_visible n (m : dfact * option node_id) :=
    let '(f, _) := m in output_visible n f.

  Definition finput_at dst (m : dfact * option node_id) :=
    let '(f, _) := m in existsb (eqb dst) (input_locs (dfact_rel f)).

  Definition fforward (src : node_id) (mn : rel * option node_id) : list node_id :=
    get_or_default (get_or_default fts src) mn.

  Definition corresp (e : IO_event) (e' : fIO_event) : Prop :=
    match e with
    | O_event lbl msgs => exists msgs', e' = O_event lbl msgs' /\ msgs = map fst msgs'
    | I_event msg => e' = I_event (msg, None)
    end.

  Definition fgraph_step g1 e g2 :=
    exists e',
      corresp e e' /\
        graph_step
          (fun src dst '(f, orig) => existsb (eqb dst) (fforward src (dfact_rel f, orig)))
          finput_at
          foutput_visible
          (fun n => fnode_step node_step (fprog_at n) n)
          g1 e' g2.

  Definition forwarding_graph (mn : rel * option node_id) :=
    map.fold (fun g src tbl => graph.put_edges g src (get_or_default tbl mn)) graph.empty fts.

  Definition recipients (orig : option node_id) R : list node_id :=
    match orig with
    | Some n => nforward n R
    | None => input_locs R
    end.

  Definition ngraph_step :=
    graph_step
      (fun src dst m => existsb (eqb dst) (nforward src (dfact_rel m)))
      (fun dst m => existsb (eqb dst) (input_locs (dfact_rel m)))
      output_visible
      (fun n => node_step (fprog_at n).(fnode_rules)).

  Definition forwarding_tree :=
    forall R n,
      graph.is_locally_tree (forwarding_graph (R, Some n)) n.

  Definition forwarding_reaches :=
    forall R n n',
      In n' (nforward n R) ->
      graph.reaches (forwarding_graph (R, Some n)) n n'.

  Definition can_make_it R orig cur destn :=
    In destn (recipients orig R) /\ graph.reaches (forwarding_graph (R, orig)) cur destn.

  Definition incoming_msgs (fs : fgraph_state) (destn : node_id) : list dfact -> Prop :=
    flat_map_Prop (fun '(cur, ns) =>
                   fun msgs =>
                     exists msgs_lbls,
                       filter_Prop (fun '(f, orig) => can_make_it (dfact_rel f) orig cur destn)
                         (ns.(gns_queue) ++ ns.(gns_node_state).(fnode_pending))
                         msgs_lbls /\
                         msgs = map fst msgs_lbls)
      (map.tuples fs).

  Definition forwarding_R
    (s1 : fgraph_state) (t1 : list IO_event)
    (s2 : ngraph_state) (t2 : list nIO_event) : Prop :=
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
    cbv [weak_sim]. intros. cbv [fgraph_step] in H0. fwd. invert H0p1.
    - destruct e; simpl in H0p0; fwd. 2: congruence.
      simpl. do 2 eexists. split.
      + apply star_one. apply gstep_input.
      + simpl. split; [reflexivity|]. admit.
    -
  Admitted.
End __.
