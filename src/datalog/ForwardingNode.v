From Stdlib Require Import List Lia Permutation Classical_Prop RelationClasses.
From Datalog Require Import List Datalog Smallstep Tactics Graph Map Default Eqb Node.
From GraphSearch Require Import GraphInterface Examples.
From coqutil Require Import Map.Interface.
From coqutil Require Import Eqb Semantics.OmniSmallstepCombinators Tactics Tactics.fwd.
Import ListNotations.

Section __.
  Context {node_prog node_state : Type}.
  Context {message label : Type}.
  Context (node_step : node_prog -> node_state -> IO_event label message -> node_state -> Prop).

  Record fnode_prog :=
    { fnode_rules : node_prog;
      fnode_keep : message -> option node_id -> bool
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
    (if fp.(fnode_keep) f orig
     then node_step fp.(fnode_rules) fs.(fnode_node) (I_event f) ns'
     else ns' = fs.(fnode_node)) ->
    fnode_step _ _ fs (O_event (forward_label f) [(f, orig)])
               {| fnode_node := ns'; fnode_pending := q1 ++ q2 |}.

End __.
Arguments fnode_prog : clear implicits.
Arguments fnode_label : clear implicits.
Arguments fnode_state : clear implicits.

Definition pebble_step {V X} {gi : graph.graph V} (g : gi) (ps1 ps2 : list (V * X)) : Prop :=
  exists v x rest,
    Permutation ps1 ((v, x) :: rest) /\
    Permutation ps2 (map (fun v' => (v', x)) (graph.edges g v) ++ rest).

Definition graph_incoming {V X} {eqbV : Eqb V} {gi : graph.graph V}
  (g : gi) (target : V) (ps : list (V * X)) : list X :=
  map snd (filter (fun '(v, _) => graph.reachesb g v target) ps).

Section __.
  Context {rel : relT} {T : valueT}.
  Context {rel_eqb : Eqb rel}.
  Context {node_prog node_state : Type}.
  Context {label : Type}.
  Context (node_step : node_prog -> node_state -> IO_event label dfact -> node_state -> Prop).
  Context (finput_locs : rel -> list node_id).
  Context (ninput_locs : rel -> list node_id).
  Context (output_visible : node_id -> dfact -> bool).
  Context (nforward : node_id -> rel -> list node_id).
  Context {forwarding_table : map.map (rel * option node_id) (list node_id)}.
  Context {forwarding_tables : map.map node_id forwarding_table}.
  Context {graph : graph.graph (option node_id)}.
  Context (fts : forwarding_tables).
  Context (prog_at : node_id -> node_prog).

  Local Notation fgraph_node_state :=
    (graph_node_state (dfact * option node_id) (fnode_label dfact label) (fnode_state node_state dfact)).
  Local Notation ngraph_node_state := (graph_node_state dfact label node_state).

  Context {fgraph_state : map.map node_id fgraph_node_state}.
  Context {fgraph_state_ok : map.ok fgraph_state}.
  Context {ngraph_state : map.map node_id ngraph_node_state}.
  Context {ngraph_state_ok : map.ok ngraph_state}.

  Local Notation flabel := (graph_label (dfact * option node_id) (fnode_label dfact label)).
  Local Notation nlabel := (graph_label dfact label).
  Local Notation IO_event := (Smallstep.IO_event flabel dfact).
  Local Notation fIO_event := (Smallstep.IO_event flabel (dfact * option node_id)).
  Local Notation nIO_event := (Smallstep.IO_event nlabel dfact).
  Local Notation pebble := (option node_id * dfact)%type.

  Definition recipients (orig : option node_id) R : list node_id :=
    match orig with
    | Some n => nforward n R
    | None => ninput_locs R
    end.

  Definition recipients_of (m : dfact * option node_id) :=
    let '(f, o) := m in recipients o (dfact_rel f).

  Definition fprog_at n : fnode_prog node_prog dfact :=
    {| fnode_rules := prog_at n;
       fnode_keep := fun f orig => existsb (eqb n) (recipients_of (f, orig)) |}.

  Definition foutput_visible n (m : dfact * option node_id) :=
    let '(f, _) := m in output_visible n f.

  Definition finput_at dst (m : dfact * option node_id) :=
    let '(f, _) := m in existsb (eqb dst) (finput_locs (dfact_rel f)).

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
    let g := map.fold (fun g src tbl => graph.put_edges g (Some src) (map Some (get_or_default tbl mn))) graph.empty fts in
    graph.put_edges g None (map Some (finput_locs (fst mn))).

  Definition ngraph_step :=
    graph_step
      (fun src dst m => existsb (eqb dst) (nforward src (dfact_rel m)))
      (fun dst m => existsb (eqb dst) (ninput_locs (dfact_rel m)))
      output_visible
      (fun n => node_step (fprog_at n).(fnode_rules)).

  Definition forwarding_tree :=
    forall R orig,
      graph.is_locally_tree (forwarding_graph (R, orig)) orig.

  Definition forwarding_reaches :=
    forall R orig n',
      In n' (recipients orig R) ->
      graph.reaches (forwarding_graph (R, orig)) orig (Some n').

  Definition all_pending_msgs (ns : fgraph_node_state) :=
    ns.(gns_queue) ++ ns.(gns_node_state).(fnode_pending).

  Lemma all_pending_msgs_enqueue ms (ns : fgraph_node_state) :
    all_pending_msgs (enqueue ms ns) = ms ++ all_pending_msgs ns.
  Proof.
    cbv [all_pending_msgs]. cbn [enqueue gns_queue gns_node_state].
    rewrite <- app_assoc. reflexivity.
  Qed.

  Definition msg_matches (R : rel) (orig : option node_id) (m : dfact * option node_id) : bool :=
    let '(f, o) := m in eqb R (dfact_rel f) && eqb orig o.

  Definition to_pebbles (R : rel) (orig : option node_id) (fg : fgraph_state) : list pebble :=
    flat_map (fun '(n, ns) =>
      map (fun '(f, _) => (Some n, f))
        (filter (msg_matches R orig) (all_pending_msgs ns)))
      (map.tuples fg).

  Lemma to_pebbles_enqueue R orig (s : fgraph_state) cur v ms :
    map.get s cur = Some v ->
    Permutation (to_pebbles R orig (map.put s cur (enqueue ms v)))
                (map (fun '(f, _) => (Some cur, f)) (filter (msg_matches R orig) ms)
                 ++ to_pebbles R orig s).
  Proof.
    intros Hget. cbv [to_pebbles].
    rewrite (tuples_put_perm_get s cur (enqueue ms v)). cbn [flat_map].
    rewrite all_pending_msgs_enqueue, filter_app, map_app, <- app_assoc.
    apply Permutation_app_head.
    rewrite (tuples_get_perm s cur v Hget). cbn [flat_map]. reflexivity.
  Qed.

  Definition forwarding_R
    (s1 : fgraph_state) (t1 : list IO_event)
    (s2 : ngraph_state) (t2 : list nIO_event) : Prop :=
    flat_map inputs_of t1 = flat_map inputs_of t2 /\
      Forall2_map (fun destn fgns ngns =>
                     fgns.(gns_node_state).(fnode_node) = ngns.(gns_node_state) /\
                       exists queue' : list (dfact * option node_id),
                         ngns.(gns_queue) = map fst queue' /\
                         Forall (fun m => In destn (recipients_of m)) queue' /\
                         forall R orig,
                           In destn (recipients orig R) ->
                           Permutation
                             (graph_incoming (forwarding_graph (R, orig)) (Some destn) (to_pebbles R orig s1))
                             (map fst (filter (msg_matches R orig) queue')))
        s1 s2.

  Lemma fgraph_weak_sims_ngraph :
    weak_sim fgraph_step ngraph_step forwarding_R.
  Proof.
    cbv [weak_sim]. intros. cbv [fgraph_step] in H0. fwd. invert H0p1.
    - destruct e; simpl in H0p0; fwd. 2: congruence.
      do 2 eexists. split.
      { apply star_one. apply gstep_input. }
      split; [reflexivity|]. cbv [forwarding_R] in *. fwd. split.
      { simpl. f_equal. assumption. }
      simpl. apply Forall2_map_map_values'_l, Forall2_map_map_values'_r.
      eapply Forall2_map_impl; [eassumption|]. simpl. intros. fwd.
      split; [assumption|].
      eexists ((if existsb (eqb k) (ninput_locs (dfact_rel d)) then [(d, None)] else []) ++ _).
      split.
      { Tactics.destruct_one_match; simpl; try eassumption || reflexivity. f_equal.
        assumption. }
      split.
      { apply Forall_app. split; [|assumption]. Tactics.destruct_one_match.
        - apply Exists_exists in E. fwd. auto.
        - auto. }
      intros R o HR.
        intros. cbv [graph_incoming].

  Admitted.
End __.
