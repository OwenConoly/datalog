From Stdlib Require Import List Lia Permutation Classical_Prop RelationClasses Morphisms Relations.
From Datalog Require Import List Datalog Smallstep Tactics Graph Map Default Eqb Node.
From GraphSearch Require Import GraphInterface Examples.
From coqutil Require Import Map.Interface Map.Properties.
From coqutil Require Import Eqb Semantics.OmniSmallstepCombinators Tactics Tactics.fwd.
Import ListNotations.

Definition loc_of_source (s : source) : location :=
  match s with
  | node_source n => node_loc n
  | input_source => input_loc
  end.

Definition loc_of_dest (d : destn) : location :=
  match d with
  | node_destn n => node_loc n
  | output_destn => output_loc
  end.

Section __.
  Context {node_prog node_state : Type}.
  Context {message label : Type}.
  Context (node_step : node_prog -> node_state -> IO_event label message -> node_state -> Prop).

  Record fnode_prog :=
    { fnode_rules : node_prog;
      fnode_keep : message -> source -> bool
    }.

  Record fnode_state :=
    { fnode_node : node_state;
      fnode_pending : list (message * source);
    }.

  Variant fnode_label :=
    | deduce_label (_ : label)
    | forward_label (_ : message).

  Inductive fnode_step (fp : fnode_prog) (self : node_id) :
    fnode_state -> IO_event fnode_label (message * source) -> fnode_state -> Prop :=
  | fnode_input fs m :
    fnode_step _ _ fs (I_event m)
               {| fnode_node := fs.(fnode_node); fnode_pending := m :: fs.(fnode_pending) |}
  | fnode_deduce fs ns' lbl outs :
    node_step fp.(fnode_rules) fs.(fnode_node) (O_event lbl outs) ns' ->
    fnode_step _ _ fs (O_event (deduce_label lbl) [])
               {| fnode_node := ns';
                  fnode_pending := map (fun f => (f, node_source self)) outs ++ fs.(fnode_pending) |}
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

Section pebbles.
  Context {V X : Type} {eqbV : Eqb V} {gi : graph.graph V} {gok : graph.ok gi}.

  Definition pebble_step (g : gi) (v : V) (ps1 ps2 : list (V * X)) : Prop :=
    exists rest x,
      Permutation ps1 ((v, x) :: rest) /\
      Permutation ps2 (map (fun v' => (v', x)) (graph.edges g v) ++ rest).

  Definition graph_incoming (g : gi) (target : V) (ps : list (V * X)) : list X :=
    map snd (filter (fun '(v, _) => graph.reachesb g v target) ps).

  #[export] Instance graph_incoming_Proper (g : gi) (target : V) :
    Proper (@Permutation _ ==> @Permutation _) (graph_incoming g target).
  Proof.
    intros ps ps' Hp. cbv [graph_incoming].
    apply Permutation_map. apply Permutation_filter. exact Hp.
  Qed.

  Lemma graph_incoming_app (g : gi) (target : V) (ps1 ps2 : list (V * X)) :
    graph_incoming g target (ps1 ++ ps2) = graph_incoming g target ps1 ++ graph_incoming g target ps2.
  Proof.
    cbv [graph_incoming]. rewrite filter_app, map_app. reflexivity.
  Qed.

  Lemma graph_incoming_pebble_step (g : gi) v target ps1 ps2 :
    graph.is_locally_tree g v ->
    v <> target ->
    pebble_step g v ps1 ps2 ->
    Permutation (graph_incoming g target ps1) (graph_incoming g target ps2).
  Proof.
  Admitted.
End pebbles.

Section __.
  Context {rel : relT} {T : valueT}.
  Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.
  Context {node_prog node_state : Type}.
  Context {label : Type}.
  Context (node_step : node_prog -> node_state -> IO_event label dfact -> node_state -> Prop).
  Context (nforward : source -> rel -> list destn).
  Context {forwarding_table : map.map (rel * source) (list destn)}.
  Context {forwarding_tables : map.map source forwarding_table}.
  Context {forwarding_table_ok : map.ok forwarding_table}.
  Context {forwarding_tables_ok : map.ok forwarding_tables}.
  Context {graph : graph.graph location} {graph_ok : graph.ok graph}.
  Context (fts : forwarding_tables).
  Context (prog_at : node_id -> node_prog).

  Local Notation fgraph_node_state :=
    (graph_node_state (dfact * source) (fnode_label dfact label) (fnode_state node_state dfact)).
  Local Notation ngraph_node_state := (graph_node_state dfact label node_state).

  Context {fgraph_state : map.map node_id fgraph_node_state}.
  Context {fgraph_state_ok : map.ok fgraph_state}.
  Context {ngraph_state : map.map node_id ngraph_node_state}.
  Context {ngraph_state_ok : map.ok ngraph_state}.

  Local Notation flabel := (graph_label (dfact * source) (fnode_label dfact label)).
  Local Notation nlabel := (graph_label dfact label).
  Local Notation IO_event := (Smallstep.IO_event flabel dfact).
  Local Notation fIO_event := (Smallstep.IO_event flabel (dfact * source)).
  Local Notation nIO_event := (Smallstep.IO_event nlabel dfact).
  Local Notation pebble := (location * dfact)%type.

  Local Notation fgstate := (graph_state (dfact * source) (fnode_label dfact label) (fnode_state node_state dfact)).
  Local Notation ngstate := (graph_state dfact label node_state).

  Definition nforwardb (s : source) d f := inb d (nforward s (dfact_rel f)).

  Definition ngraph_step :=
    graph_step
      nforwardb
      (fun n => node_step (prog_at n)).

  Definition fforward (s : source) (mn : rel * source) : list destn :=
    get_or_default (get_or_default fts s) mn.

  Definition fforwardb s d '(f, orig) := inb d (fforward s (dfact_rel f, orig)).

  Definition corresp (e : IO_event) (e' : fIO_event) : Prop :=
    match e with
    | O_event lbl msgs => exists msgs', e' = O_event lbl msgs' /\ msgs = map fst msgs'
    | I_event msg => e' = I_event (msg, input_source)
    end.

  Definition fprog_at n : fnode_prog node_prog dfact :=
    {| fnode_rules := prog_at n;
       fnode_keep := fun f orig => inb (node_destn n) (nforward orig (dfact_rel f)) |}.

  Definition fgraph_step g1 e g2 :=
    exists e',
      corresp e e' /\
        graph_step
          fforwardb
          (fun n => fnode_step node_step (fprog_at n) n)
          g1 e' g2.

  Definition forwarding_graph (mn : rel * source) :=
    graph.of_edges
      (flat_map
         (fun '(s, tbl) => map (fun d => (loc_of_source s, loc_of_dest d)) (get_or_default tbl mn))
         (map.tuples fts)).

  Definition forwarding_tree :=
    forall R orig,
      graph.is_locally_tree (forwarding_graph (R, orig)) (loc_of_source orig).

  Definition forwarding_reaches :=
    forall R orig d,
      In d (nforward orig R) ->
      graph.reaches (forwarding_graph (R, orig)) (loc_of_source orig) (loc_of_dest d).

  Definition no_extra_outputs :=
    forall R orig,
      graph.reaches (forwarding_graph (R, orig)) (loc_of_source orig) output_loc ->
      In output_destn (nforward orig R).

  Lemma forwarding_graph_spec mn u w :
    graph.edge (forwarding_graph mn) u w <->
    exists s d, In d (fforward s mn) /\ u = loc_of_source s /\ w = loc_of_dest d.
  Proof.
    unfold forwarding_graph, fforward. rewrite graph.edge_of_edges, in_flat_map. split.
    - intros ([s tbl] & Htup & Hin). apply map.tuples_spec in Htup.
      apply in_map_iff in Hin. destruct Hin as (d & Heq & Hind).
      inversion Heq; subst. exists s, d. rewrite (get_or_default_Some _ _ _ Htup). auto.
    - intros (s & d & Hind & -> & ->). destruct (map.get fts s) as [tbl|] eqn:Hget.
      + rewrite (get_or_default_Some _ _ _ Hget) in Hind.
        exists (s, tbl). split; [ apply map.tuples_spec; exact Hget | ].
        apply in_map_iff. exists d. auto.
      + exfalso. cbv [get_or_default get_or] in Hind. rewrite Hget in Hind.
        cbv [default map_default list_default] in Hind. rewrite map.get_empty in Hind.
        cbn [In] in Hind. exact Hind.
  Qed.

  Definition all_pending_msgs (ns : fgraph_node_state) :=
    ns.(gns_queue) ++ ns.(gns_node_state).(fnode_pending).

  Lemma all_pending_msgs_enqueue ms (ns : fgraph_node_state) :
    all_pending_msgs (enqueue ms ns) = ms ++ all_pending_msgs ns.
  Proof.
    cbv [all_pending_msgs]. cbn [enqueue gns_queue gns_node_state].
    rewrite <- app_assoc. reflexivity.
  Qed.

  Definition msg_matches (R : rel) (orig : source) (m : dfact * source) : bool :=
    let '(f, o) := m in eqb R (dfact_rel f) && eqb orig o.

  Definition dest_msgs (s1 : fgstate) : list (destn * (dfact * source)) :=
    flat_map (fun '(n, ns) => map (fun m => (node_destn n, m)) (all_pending_msgs ns))
             (map.tuples s1.(graph_nodes))
    ++ map (fun m => (output_destn, m)) s1.(graph_output_queue).

  Definition msgs_to_pebbles (R : rel) (orig : source) (dm : list (destn * (dfact * source))) : list pebble :=
    map (fun '(d, (f, _)) => (loc_of_dest d, f)) (filter (fun '(_, m) => msg_matches R orig m) dm).

  Definition to_pebbles (R : rel) (orig : source) (s1 : fgstate) : list pebble :=
    msgs_to_pebbles R orig (dest_msgs s1).

  Lemma msgs_to_pebbles_app R orig a b :
    msgs_to_pebbles R orig (a ++ b) = msgs_to_pebbles R orig a ++ msgs_to_pebbles R orig b.
  Proof. cbv [msgs_to_pebbles]. rewrite filter_app, map_app. reflexivity. Qed.

  #[export] Instance msgs_to_pebbles_Proper R orig :
    Proper (@Permutation _ ==> @Permutation _) (msgs_to_pebbles R orig).
  Proof. intros a b H. cbv [msgs_to_pebbles]. apply Permutation_map, Permutation_filter, H. Qed.

  Lemma dest_msgs_map_values'_enqueue (g : node_id -> list (dfact * source)) (s : fgstate) :
    Permutation
      (dest_msgs {| graph_nodes := map_values' (fun n ns => enqueue (g n) ns) s.(graph_nodes);
                    graph_output_queue := s.(graph_output_queue) |})
      (flat_map (fun '(n, _) => map (fun m => (node_destn n, m)) (g n)) (map.tuples s.(graph_nodes))
       ++ dest_msgs s).
  Proof.
    cbv [dest_msgs]. cbn [graph_nodes graph_output_queue].
    rewrite tuples_map_values', flat_map_map, app_assoc.
    apply Permutation_app_tail. apply flat_map_app_perm. intros [n ns]. cbv beta iota.
    rewrite all_pending_msgs_enqueue, map_app. reflexivity.
  Qed.

  Lemma dest_msgs_output_append oms (s : fgstate) :
    Permutation
      (dest_msgs {| graph_nodes := s.(graph_nodes); graph_output_queue := oms ++ s.(graph_output_queue) |})
      (map (fun m => (output_destn, m)) oms ++ dest_msgs s).
  Proof.
    cbv [dest_msgs]. cbn [graph_nodes graph_output_queue].
    rewrite map_app. apply Permutation_app_swap_app.
  Qed.

  Lemma dest_msgs_get_remove (s : fgstate) n ns :
    map.get s.(graph_nodes) n = Some ns ->
    Permutation
      (dest_msgs s)
      (map (fun m => (node_destn n, m)) (all_pending_msgs ns)
       ++ dest_msgs {| graph_nodes := map.remove s.(graph_nodes) n; graph_output_queue := s.(graph_output_queue) |}).
  Proof.
    intros Hget. cbv [dest_msgs]. cbn [graph_nodes graph_output_queue].
    rewrite (tuples_get_perm _ _ _ Hget). cbn [flat_map].
    rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma dest_msgs_put (s : fgstate) n v v' new :
    map.get s.(graph_nodes) n = Some v ->
    Permutation (all_pending_msgs v') (new ++ all_pending_msgs v) ->
    Permutation
      (dest_msgs {| graph_nodes := map.put s.(graph_nodes) n v';
                    graph_output_queue := s.(graph_output_queue) |})
      (map (fun m => (node_destn n, m)) new ++ dest_msgs s).
  Proof.
    intros Hget Hperm.
    erewrite dest_msgs_get_remove with (n := n) (ns := v').
    2: { cbn [graph_nodes]. apply map.get_put_same. }
    cbn [graph_nodes graph_output_queue]. rewrite map.remove_put_same.
    rewrite (dest_msgs_get_remove s n v Hget), app_assoc, <- map_app.
    apply Permutation_app_tail. apply Permutation_map. exact Hperm.
  Qed.

  Lemma to_pebbles_map_values'_enqueue R orig (g : node_id -> list (dfact * source)) (s : fgstate) :
    Permutation
      (to_pebbles R orig {| graph_nodes := map_values' (fun n ns => enqueue (g n) ns) s.(graph_nodes);
                            graph_output_queue := s.(graph_output_queue) |})
      (msgs_to_pebbles R orig
         (flat_map (fun '(n, _) => map (fun m => (node_destn n, m)) (g n)) (map.tuples s.(graph_nodes)))
       ++ to_pebbles R orig s).
  Proof.
    unfold to_pebbles. rewrite dest_msgs_map_values'_enqueue, msgs_to_pebbles_app. reflexivity.
  Qed.

  Lemma to_pebbles_map_values'_enqueue_nomatch R orig
    (g : node_id -> list (dfact * source)) (s : fgstate) :
    (forall n m, In m (g n) -> msg_matches R orig m = false) ->
    Permutation
      (to_pebbles R orig {| graph_nodes := map_values' (fun n ns => enqueue (g n) ns) s.(graph_nodes);
                            graph_output_queue := s.(graph_output_queue) |})
      (to_pebbles R orig s).
  Proof.
    intros Hnm. rewrite to_pebbles_map_values'_enqueue.
    match goal with |- Permutation (?d ++ _) _ => assert (Hd : d = []) end.
    { cbv [msgs_to_pebbles]. erewrite filter_ext_in with (g := fun _ => false).
      - rewrite filter_false. reflexivity.
      - intros [d' m] Hin. apply in_flat_map in Hin. destruct Hin as [[k ns] [_ Hin]].
        apply in_map_iff in Hin. destruct Hin as [m' [Heq Hin']]. injection Heq as _ Hm.
        cbn. rewrite <- Hm. apply (Hnm k m' Hin'). }
    rewrite Hd. reflexivity.
  Qed.

  Lemma to_pebbles_output_append R orig oms (s : fgstate) :
    Permutation
      (to_pebbles R orig {| graph_nodes := s.(graph_nodes);
                            graph_output_queue := oms ++ s.(graph_output_queue) |})
      (msgs_to_pebbles R orig (map (fun m => (output_destn, m)) oms) ++ to_pebbles R orig s).
  Proof.
    unfold to_pebbles. rewrite dest_msgs_output_append, msgs_to_pebbles_app. reflexivity.
  Qed.

  Lemma to_pebbles_get_remove R orig (s : fgstate) n ns :
    map.get s.(graph_nodes) n = Some ns ->
    Permutation
      (to_pebbles R orig s)
      (msgs_to_pebbles R orig (map (fun m => (node_destn n, m)) (all_pending_msgs ns))
       ++ to_pebbles R orig {| graph_nodes := map.remove s.(graph_nodes) n;
                               graph_output_queue := s.(graph_output_queue) |}).
  Proof.
    intros Hget. unfold to_pebbles at 1.
    rewrite (dest_msgs_get_remove _ _ _ Hget), msgs_to_pebbles_app. reflexivity.
  Qed.

  Definition forwarding_compatible {V} {M : map.map node_id V} (s : M) :=
    forall n, map.get s n <> None <-> map.get fts (node_source n) <> None.

  Context (forwarding_wf :
            forall s ms n, fforwardb s (node_destn n) ms = true -> map.get fts (node_source n) <> None).

  Lemma forwarding_compatible_same_domain {V1} {M1 : map.map node_id V1}
    {V2} {M2 : map.map node_id V2} (s : M1) (s' : M2) :
    forwarding_compatible s ->
    same_domain s s' ->
    forwarding_compatible s'.
  Proof.
    intros Hcompat Hsd n. rewrite <- (Hcompat n).
    pose proof (Forall2_map_get_None _ _ _ n Hsd) as Hnone.
    split.
    - intros Hne Heq. apply Hne. apply (proj1 Hnone). exact Heq.
    - intros Hne Heq. apply Hne. apply (proj2 Hnone). exact Heq.
  Qed.

  Lemma forward_to_same_domain keep msgs (gs : fgstate) :
    same_domain gs.(graph_nodes) (forward_to keep msgs gs).(graph_nodes).
  Proof.
    cbn [forward_to graph_nodes]. apply same_domain_map_values'.
  Qed.

  Lemma forward_to_nil keep (gs : fgstate) :
    forward_to keep [] gs = gs.
  Proof.
    destruct gs as [gn goq]. cbv [forward_to]. cbn [filter]. rewrite app_nil_l. f_equal.
    erewrite map_values'_ext.
    - apply map_values'_id.
    - intros k v. destruct v; reflexivity.
  Qed.

  Definition travelling_to (dm : list (destn * (dfact * source))) (dest : destn) (queue : list dfact) : Prop :=
    exists queue' : list (dfact * source),
      queue = map fst queue' /\
      Forall (fun '(f, orig) => In dest (nforward orig (dfact_rel f))) queue' /\
      forall R orig,
        In dest (nforward orig R) ->
        Permutation
          (graph_incoming (forwarding_graph (R, orig)) (loc_of_dest dest) (msgs_to_pebbles R orig dm))
          (map fst (filter (msg_matches R orig) queue')).

  #[export] Instance travelling_to_Proper :
    Proper (@Permutation _ ==> eq ==> eq ==> iff) travelling_to.
  Proof.
    intros dm dm' Hp d d' Hd q q' Hq. subst.
    unfold travelling_to. setoid_rewrite Hp. reflexivity.
  Qed.

  Lemma travelling_to_app dmA dmB dest queueA queueB :
    travelling_to dmA dest queueA ->
    travelling_to dmB dest queueB ->
    travelling_to (dmA ++ dmB) dest (queueA ++ queueB).
  Proof.
    intros (qA & HqA & HFA & HPA) (qB & HqB & HFB & HPB). subst queueA queueB.
    exists (qA ++ qB). split; [ | split ].
    - rewrite map_app. reflexivity.
    - apply Forall_app. split; [ exact HFA | exact HFB ].
    - intros R orig Hin.
      rewrite msgs_to_pebbles_app, graph_incoming_app, filter_app, map_app.
      apply Permutation_app.
      + apply HPA. exact Hin.
      + apply HPB. exact Hin.
  Qed.

  Lemma travelling_to_incl dm dest queue :
    travelling_to dm dest queue ->
    incl queue (map (fun '(_, (f, _)) => f) dm).
  Proof.
    intros (queue' & Hq & HF & HP) f Hf. subst queue.
    apply in_map_iff in Hf. destruct Hf as ((f', orig) & Heq & Hin).
    simpl in Heq. subst f'.
    rewrite Forall_forall in HF. specialize (HF _ Hin). simpl in HF.
    specialize (HP (dfact_rel f) orig HF).
    assert (Hrhs : In f (map fst (filter (msg_matches (dfact_rel f) orig) queue'))).
    { apply in_map_iff. exists (f, orig). split; [reflexivity|].
      apply filter_In. split; [exact Hin|].
      cbn [msg_matches]. rewrite !eqb_refl_true by typeclasses eauto. reflexivity. }
    assert (Hlhs : In f (graph_incoming (forwarding_graph (dfact_rel f, orig))
                                        (loc_of_dest dest)
                                        (msgs_to_pebbles (dfact_rel f) orig dm))).
    { eapply Permutation_in; [ symmetry; exact HP | exact Hrhs ]. }
    cbv [graph_incoming] in Hlhs. apply in_map_iff in Hlhs.
    destruct Hlhs as ((loc, f2) & Hsnd & Hin2). simpl in Hsnd. subst f2.
    apply filter_In in Hin2. destruct Hin2 as [Hin2 _].
    cbv [msgs_to_pebbles] in Hin2. apply in_map_iff in Hin2.
    destruct Hin2 as ((d, (f3, o3)) & Heq3 & Hin3).
    apply filter_In in Hin3. destruct Hin3 as [Hin3 _].
    inversion Heq3. subst.
    apply in_map_iff. exists (d, (f, o3)). split; [reflexivity | exact Hin3].
  Qed.

  Lemma travelling_to_in dm dest queue f orig :
    travelling_to dm dest queue ->
    In (dest, (f, orig)) dm ->
    In dest (nforward orig (dfact_rel f)) ->
    In f queue.
  Proof.
    intros (queue' & Hq & HF & HP) Hin Hprem. subst queue.
    specialize (HP (dfact_rel f) orig Hprem).
    assert (Hlhs : In f (graph_incoming (forwarding_graph (dfact_rel f, orig))
                                        (loc_of_dest dest)
                                        (msgs_to_pebbles (dfact_rel f) orig dm))).
    { cbv [graph_incoming]. apply in_map_iff. exists (loc_of_dest dest, f). split; [reflexivity|].
      apply filter_In. split.
      - cbv [msgs_to_pebbles]. apply in_map_iff. exists (dest, (f, orig)).
        split; [reflexivity|]. apply filter_In. split; [exact Hin|].
        cbn [msg_matches]. rewrite !eqb_refl_true by typeclasses eauto. reflexivity.
      - destr (graph.reachesb (forwarding_graph (dfact_rel f, orig)) (loc_of_dest dest) (loc_of_dest dest));
          [ reflexivity | exfalso; eauto using graph.reaches_self ]. }
    eapply Permutation_in in Hlhs; [| exact HP].
    apply in_map_iff in Hlhs. destruct Hlhs as ((f2, o2) & Hfst & Hin2). simpl in Hfst. subst f2.
    apply filter_In in Hin2. destruct Hin2 as [Hin2 _].
    apply in_map_iff. exists (f, o2). split; [reflexivity | exact Hin2].
  Qed.

  Definition queue_at_dest {M L NS} {nm : map.map node_id (graph_node_state M L NS)}
    (s : @graph_state M L NS nm) (d : destn) :=
    match d with
    | node_destn n => unwrap_or_default (option_map gns_queue (map.get s.(graph_nodes) n))
    | output_destn => s.(graph_output_queue)
    end.

  Definition valid_dest d :=
    match d with
    | output_destn => True
    | node_destn n => map.get fts (node_source n) <> None
    end.

  Lemma queue_at_dest_forward_to keep msgs (s : ngstate) dest :
    forwarding_compatible s.(graph_nodes) ->
    valid_dest dest ->
    queue_at_dest (forward_to keep msgs s) dest
    = filter (keep dest) msgs ++ queue_at_dest s dest.
  Proof.
    intros Hcompat Hvalid. destruct dest as [n|].
    - cbv [valid_dest] in Hvalid. apply (proj2 (Hcompat n)) in Hvalid.
      destruct (map.get s.(graph_nodes) n) as [ns|] eqn:Hns; [ | congruence ].
      cbv [queue_at_dest forward_to]. cbn [graph_nodes graph_output_queue].
      rewrite get_map_values', Hns.
      cbn [option_map unwrap_or_default unwrap_or gns_queue enqueue]. reflexivity.
    - cbv [queue_at_dest forward_to]. cbn [graph_nodes graph_output_queue]. reflexivity.
  Qed.

  Lemma queue_at_dest_ext (sa sb : ngstate) dest :
    (forall n, option_map gns_queue (map.get sa.(graph_nodes) n)
             = option_map gns_queue (map.get sb.(graph_nodes) n)) ->
    sa.(graph_output_queue) = sb.(graph_output_queue) ->
    queue_at_dest sa dest = queue_at_dest sb dest.
  Proof.
    intros Hq Hout. destruct dest as [m|].
    - cbn [queue_at_dest]. rewrite Hq. reflexivity.
    - cbn [queue_at_dest]. exact Hout.
  Qed.

  Definition wf_queues (s1 : fgstate) :=
    forall dest f orig,
      In (f, orig) (queue_at_dest s1 dest) ->
      In dest (nforward orig (dfact_rel f)).

  Definition forwarding_R
    (s1 : fgstate) (t1 : list IO_event)
    (s2 : ngstate) (t2 : list nIO_event) : Prop :=
    flat_map inputs_of t1 = flat_map inputs_of t2 /\
      flat_map outputs_of t1 = flat_map outputs_of t2 /\
      forwarding_compatible s1.(graph_nodes) /\
      wf_queues s1 /\
      Forall2_map (fun _ fgns ngns =>
                     fgns.(gns_node_state).(fnode_node) = ngns.(gns_node_state))
        s1.(graph_nodes) s2.(graph_nodes) /\
      (forall dest, valid_dest dest -> travelling_to (dest_msgs s1) dest (queue_at_dest s2 dest)).

  Lemma forwarding_R_output_incl s1 t1 s2 t2 :
    forwarding_R s1 t1 s2 t2 ->
    incl s2.(graph_output_queue) (map (fun '(_, (f, _)) => f) (dest_msgs s1)).
  Proof.
    intros HR. cbv [forwarding_R] in HR. fwd.
    apply (travelling_to_incl (dest_msgs s1) output_destn). apply HRp5. exact I.
  Qed.

  Lemma in_queue_at_dest_dest_msgs (s : fgstate) dest m :
    In m (queue_at_dest s dest) ->
    In (dest, m) (dest_msgs s).
  Proof.
    intros Hin. cbv [dest_msgs]. apply in_or_app. destruct dest as [n|].
    - left. cbn [queue_at_dest] in Hin.
      destruct (map.get s.(graph_nodes) n) as [ns|] eqn:Hget.
      2: { cbn [option_map unwrap_or_default unwrap_or default list_default] in Hin.
           destruct Hin. }
      cbn [option_map unwrap_or_default unwrap_or] in Hin.
      apply in_flat_map. exists (n, ns). split.
      + apply map.tuples_spec. exact Hget.
      + apply in_map_iff. exists m. split; [reflexivity|].
        cbv [all_pending_msgs]. apply in_or_app. left. exact Hin.
    - right. cbn [queue_at_dest] in Hin.
      apply in_map_iff. exists m. split; [reflexivity | exact Hin].
  Qed.

  Lemma forwarding_R_queue_incl s1 t1 s2 t2 dest :
    forwarding_R s1 t1 s2 t2 ->
    valid_dest dest ->
    (forall f orig, In (f, orig) (queue_at_dest s1 dest) ->
                    In dest (nforward orig (dfact_rel f))) ->
    incl (map fst (queue_at_dest s1 dest)) (queue_at_dest s2 dest).
  Proof.
    intros HR Hvalid Hwf. cbv [forwarding_R] in HR. fwd.
    specialize (HRp5 dest Hvalid).
    intros f Hf. apply in_map_iff in Hf. destruct Hf as ((f', orig) & Heq & Hin).
    simpl in Heq. subst f'.
    apply (travelling_to_in _ dest _ f orig HRp5).
    - apply in_queue_at_dest_dest_msgs. exact Hin.
    - apply Hwf. exact Hin.
  Qed.

  Lemma wf_queues_incl (sa sb : fgstate) :
    (forall dest, incl (queue_at_dest sa dest) (queue_at_dest sb dest)) ->
    wf_queues sb ->
    wf_queues sa.
  Proof.
    intros Hincl Hsb dest f orig Hin. apply Hsb. apply Hincl. exact Hin.
  Qed.

  Lemma queue_at_dest_put_incl (s : fgstate) n ns ns' dest :
    map.get s.(graph_nodes) n = Some ns ->
    incl ns'.(gns_queue) ns.(gns_queue) ->
    incl (queue_at_dest {| graph_nodes := map.put s.(graph_nodes) n ns';
                           graph_output_queue := s.(graph_output_queue) |} dest)
         (queue_at_dest s dest).
  Proof.
    intros Hget Hincl. destruct dest as [k|].
    - cbn [queue_at_dest graph_nodes]. destr (eqb n k).
      + subst. rewrite map.get_put_same, Hget.
        cbn [option_map unwrap_or_default unwrap_or]. exact Hincl.
      + rewrite map.get_put_diff by congruence. apply incl_refl.
    - cbn [queue_at_dest graph_output_queue]. apply incl_refl.
  Qed.

  Hint Constructors NoDup : core.

  Lemma forwarding_edge_target mn loc w :
    In w (graph.edges (forwarding_graph mn) loc) ->
    (exists n, w = node_loc n) \/ w = output_loc.
  Proof.
    intros Hin. apply (proj1 (forwarding_graph_spec mn loc w)) in Hin.
    fwd. destruct d; simpl; eauto.
  Qed.

  Lemma pebble_step_forward (s : fgstate) R orig src (msgs : list (dfact * source)) :
    forwarding_compatible s.(graph_nodes) ->
    clos_refl_trans_1n _ (pebble_step (forwarding_graph (R, orig)) (loc_of_source src))
      (map (fun '(f, _) => (loc_of_source src, f)) (filter (msg_matches R orig) msgs)
       ++ to_pebbles R orig s)
      (to_pebbles R orig (forward_to (fforwardb src) msgs s)).
  Proof.
  (*   intros Hcompat. cbv [pebble_step]. eexists. split; [ reflexivity | ]. *)
  (*   set (es := graph.edges (forwarding_graph (dfact_rel f, orig)) loc). *)
  (*   etransitivity; [ apply to_pebbles_map_values'_enqueue | ]. *)
  (*   etransitivity; [ apply Permutation_app_head, to_pebbles_output_event | ]. *)
  (*   rewrite app_assoc. apply Permutation_app; [ | reflexivity ]. *)
  (*   (* the single output event contributes exactly the output pebble, when there is one *) *)
  (*   replace (map (fun '(f0, _) => (output_loc, f0)) *)
  (*              (filter (msg_matches (dfact_rel f) orig) *)
  (*                 (filter (fun _ => inb output_loc es) [(f, orig)]))) *)
  (*     with (if inb output_loc es then [(output_loc, f)] else []). *)
  (*   2:{ destruct (inb output_loc es); [ | reflexivity ]. *)
  (*       cbn [msg_matches filter]. rewrite !eqb_refl_true by typeclasses eauto. reflexivity. } *)
  (*   apply NoDup_Permutation. *)
  (*   - apply NoDup_app. *)
  (*     + apply List.NoDup_flat_map. *)
  (*       -- apply map.tuples_NoDup. *)
  (*       -- intros [n ns] _. simpl. *)
  (*         Tactics.destruct_one_match; try solve [simpl; auto]. *)
  (*         cbn [filter]. Tactics.destruct_one_match; simpl; auto. *)
  (*       -- intros [? ?] [? ?]. intros. rewrite in_map_iff in *. fwd. *)
  (*          rewrite map.tuples_spec in *. congruence. *)
  (*     + Tactics.destruct_one_match; auto. *)
  (*   + intros [? ? ] H. apply in_flat_map in H. fwd. Tactics.destruct_one_match_hyp. *)
  (*     apply in_map_iff in Hp1. fwd. Tactics.destruct_one_match; auto. simpl. *)
  (*     intros [?|?]; congruence. *)
  (*   - apply FinFun.Injective_map_NoDup. *)
  (*     + intros ? ? Heq. congruence. *)
  (*     + apply graph.edges_NoDup. *)
  (*   - intros [v x]. rewrite in_app_iff. split. *)
  (*     + intros [Hnode | Hout]. *)
  (*       * apply in_flat_map in Hnode. destruct Hnode as [[n ns] [_ Hnode]]. *)
  (*         apply in_map_iff in Hnode. destruct Hnode as [[f0 o0] [Hvx Hnode]]. *)
  (*         apply filter_In in Hnode. destruct Hnode as [Hnode _]. *)
  (*         apply filter_In in Hnode. destruct Hnode as [[ [= <- <-] | [] ] Hedge]. *)
  (*         apply in_map_iff. exists (node_loc n). split; [ exact Hvx | ]. *)
  (*         exact (proj1 (inb_true_iff _ _) Hedge). *)
  (*       * destruct (inb output_loc es) eqn:Hoe; [ | destruct Hout ]. *)
  (*         destruct Hout as [ [= <- <-] | [] ]. *)
  (*         apply in_map_iff. exists output_loc. split; [ reflexivity | ]. *)
  (*         exact (proj1 (inb_true_iff _ _) Hoe). *)
  (*     + intros [w [Hvx Hin]] % in_map_iff. injection Hvx as <- <-. *)
  (*       destruct (forwarding_edge_target _ _ _ Hin) as [ [n ->] | -> ]. *)
  (*       * left. destruct (map.get s n) as [ns|] eqn:Hget. *)
  (*         2:{ exfalso. eapply Hcompat; eassumption. } *)
  (*         apply in_flat_map. exists (n, ns). split; [ apply map.tuples_spec; exact Hget | ]. *)
  (*         apply in_map_iff. exists (f, orig). split; [ reflexivity | ]. *)
  (*         apply filter_In. split. *)
  (*         -- apply filter_In. split; [ now left | exact (proj2 (inb_true_iff _ _) Hin) ]. *)
  (*         -- cbn [msg_matches]. rewrite !eqb_refl_true by typeclasses eauto. reflexivity. *)
  (*       * right. apply inb_true_iff in Hin. rewrite Hin. now left. *)
  (* Qed. *)
  Admitted.

  Lemma fgraph_weak_sims_ngraph :
    forwarding_reaches ->
    forwarding_tree ->
    weak_sim fgraph_step ngraph_step forwarding_R.
  Proof.
    intros Hreaches Htree.
    cbv [weak_sim]. intros. cbv [fgraph_step] in H0. fwd. invert H0p1.
    - destruct e; simpl in H0p0; fwd. 2: congruence.
      do 2 eexists. split.
      { apply star_one. apply gstep_input. }
      split; [reflexivity|]. cbv [forwarding_R] in *. fwd.
      split.
      { simpl. f_equal. assumption. }
      split.
      { simpl. assumption. }
      split.
      { eapply forwarding_compatible_same_domain; [eassumption|].
        apply forward_to_same_domain. }
      split.
      { Print wf_queues. Print queue_at_dest. admit. }
      split.
      { simpl. apply Forall2_map_map_values'_l, Forall2_map_map_values'_r.
        eapply Forall2_map_impl; [eassumption|]. simpl. intros. assumption. }
      admit.
    - destruct e; simpl in H0p0; congruence || fwd. invert H1.
      + cbv [forwarding_R] in H. fwd. pose proof H0 as H0'.
        eapply Forall2_map_get_l in H0; [|eassumption].
        simpl in H0. fwd.
        do 2 eexists. split.
        { apply star_one. apply gstep_run; try eassumption. rewrite <- H0p1.
          eassumption. }
        simpl. split; [reflexivity|]. rewrite forward_to_nil.
        cbv [forwarding_R]. simpl.
        split; [assumption|]. split; [assumption|].
        split.
        { eapply forwarding_compatible_same_domain; [eassumption|].
          eapply same_domain_put_r; eassumption. }
        split.
        { eapply wf_queues_incl; [ | eassumption ].
          intro dest. eapply queue_at_dest_put_incl; [ exact H0' | ].
          cbn [gns_queue]. apply incl_refl. }
        split.
        { apply Forall2_map_map_values'_r. simpl.
          apply Forall2_map_put_both.
          - eapply Forall2_map_impl; [eassumption|]. simpl. auto.
          - simpl. reflexivity. }
        intros. rewrite dest_msgs_put.
        2: eassumption.
        2: { cbv [all_pending_msgs]. simpl. rewrite !app_assoc.
             apply Permutation_app; [|reflexivity]. apply Permutation_app_comm. }
        rewrite map_map. rewrite queue_at_dest_forward_to.
        3: eassumption.
        2: { simpl. eapply forwarding_compatible_same_domain; [eassumption|].
             eapply same_domain_trans.
             - eapply Forall2_map_same_domain. eassumption.
             - eapply same_domain_put_r. eassumption. }
        rewrite (queue_at_dest_ext _ s2).
        2: { simpl. intros. rewrite map.get_put_dec.
             Tactics.destruct_one_match; try reflexivity.
             simpl. rewrite H0p0. reflexivity. }
        2: { reflexivity. }
        apply travelling_to_app; [|solve[auto]].
        admit.
      + simpl. do 2 eexists.
        admit.
    - destruct e; simpl in H0p0; congruence || fwd. invert H1.
      do 2 eexists. split.
      { apply star_refl. }
      split; [reflexivity|].
      cbv [forwarding_R] in *. simpl. fwd.
      split; [assumption|]. split; [assumption|]. split.
      { eapply forwarding_compatible_same_domain; [eassumption|].
        eapply same_domain_put_r. exact H0. }
      split.
      { eapply wf_queues_incl; [ | eassumption ].
        intro dest. eapply queue_at_dest_put_incl; [ exact H0 | ].
        cbn [gns_queue]. rewrite H2. intros x Hx.
        apply in_app_or in Hx. apply in_or_app.
        destruct Hx as [Hx | Hx]; [ left; exact Hx | right; right; exact Hx ]. }
      split.
      { pose proof @Forall2_map_get_l as H'. especialize H'; eauto. fwd.
        eapply Forall2_map_put_l; try eassumption.
        eapply Forall2_map_impl; [eassumption|]. auto. }
      intros. rewrite dest_msgs_put with (new := []).
      2: eassumption.
      2: { cbv [all_pending_msgs]. simpl. rewrite H2. rewrite <- !app_assoc.
           apply Permutation_app_head. symmetry. apply Permutation_middle. }
      simpl. auto.
    - destruct e; simpl in H0p0; congruence || fwd.
  Admitted.
End __.
