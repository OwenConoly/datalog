From Stdlib Require Import List Permutation Morphisms.
From Datalog Require Import List Datalog Smallstep Tactics Graph Map Default Node.
From GraphSearch Require Import GraphInterface Examples MoreTrees.
From coqutil Require Import Map.Interface Map.Properties.
From coqutil Require Import Eqb Tactics Tactics.fwd.
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

Lemma loc_of_source_inj s1 s2 :
  loc_of_source s1 = loc_of_source s2 -> s1 = s2.
Proof. destruct s1, s2; simpl; congruence. Qed.

Lemma loc_of_dest_inj d1 d2 :
  loc_of_dest d1 = loc_of_dest d2 -> d1 = d2.
Proof. destruct d1, d2; simpl; congruence. Qed.

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
      fnode_to_consume : list (message * source);
    }.

  Variant fnode_label :=
    | deduce_label (_ : label)
    | forward_label (_ : message)
    | consume_label (_ : message).

  Inductive fnode_step (fp : fnode_prog) (self : node_id) :
    fnode_state -> IO_event fnode_label (message * source) -> fnode_state -> Prop :=
  | fnode_input fs m :
    fnode_step _ _ fs (I_event m)
               {| fnode_node := fs.(fnode_node);
                  fnode_pending := m :: fs.(fnode_pending);
                  fnode_to_consume := fs.(fnode_to_consume) |}
  | fnode_deduce fs ns' lbl outs :
    node_step fp.(fnode_rules) fs.(fnode_node) (O_event lbl outs) ns' ->
    fnode_step _ _ fs (O_event (deduce_label lbl) [])
               {| fnode_node := ns';
                  fnode_pending := map (fun f => (f, node_source self)) outs ++ fs.(fnode_pending);
                  fnode_to_consume := fs.(fnode_to_consume) |}
  | fnode_route fs q1 q2 f orig :
    fs.(fnode_pending) = q1 ++ (f, orig) :: q2 ->
    fnode_step _ _ fs (O_event (forward_label f) [(f, orig)])
               {| fnode_node := fs.(fnode_node);
                  fnode_pending := q1 ++ q2;
                  fnode_to_consume :=
                    if fp.(fnode_keep) f orig
                    then (f, orig) :: fs.(fnode_to_consume)
                    else fs.(fnode_to_consume) |}
  | fnode_consume fs ns' q1 q2 f orig :
    fs.(fnode_to_consume) = q1 ++ (f, orig) :: q2 ->
    node_step fp.(fnode_rules) fs.(fnode_node) (I_event f) ns' ->
    fnode_step _ _ fs (O_event (consume_label f) [])
               {| fnode_node := ns';
                  fnode_pending := fs.(fnode_pending);
                  fnode_to_consume := q1 ++ q2 |}.

End __.
Arguments fnode_prog : clear implicits.
Arguments fnode_label : clear implicits.
Arguments fnode_state : clear implicits.

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
  Local Notation fnIO_event := (Smallstep.IO_event flabel dfact).
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

  Definition corresp (e : fnIO_event) (e' : fIO_event) : Prop :=
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

  Definition silent_event (e : fnIO_event) :=
    match e with
    | O_event (run _ (forward_label _)) _ => True
    | O_event (receive _ _) _ => True
    | _ => False
    end.

  Lemma silent_event_dec e :
    silent_event e \/ ~ silent_event e.
  Proof. destruct e as [m | lbl outs]; [ | destruct lbl as [n m | n [lbl | f | f] | m] ]; simpl; auto. Qed.

  Lemma silent_event_inputs e :
    silent_event e -> inputs_of e = [].
  Proof. destruct e as [m | lbl outs]; [ destruct 1 | reflexivity ]. Qed.


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
      injection Heq as <- <-. exists s, d. rewrite (get_or_default_Some _ _ _ Htup). auto.
    - intros (s & d & Hind & -> & ->). destruct (map.get fts s) as [tbl|] eqn:Hget.
      + rewrite (get_or_default_Some _ _ _ Hget) in Hind.
        exists (s, tbl). split; [ apply map.tuples_spec; exact Hget | ].
        apply in_map_iff. exists d. auto.
      + exfalso. cbv [get_or_default get_or] in Hind. rewrite Hget in Hind.
        cbv [default map_default list_default] in Hind. rewrite map.get_empty in Hind.
        cbn [In] in Hind. exact Hind.
  Qed.

  Lemma output_loc_reaches_only mn w :
    graph.reaches (forwarding_graph mn) output_loc w -> w = output_loc.
  Proof.
    cbv [graph.reaches graph.path_to]. intros (p & Hpath & Hlast).
    destruct p as [| v p'].
    - cbn in Hlast. exact Hlast.
    - exfalso. cbn [graph.path] in Hpath. destruct Hpath as [Hedge _].
      apply forwarding_graph_spec in Hedge. destruct Hedge as (s & d & _ & Hs & _).
      destruct s; discriminate Hs.
  Qed.

  Definition all_pending_msgs (ns : fgraph_node_state) :=
    ns.(gns_queue) ++ ns.(gns_node_state).(fnode_pending).

  Lemma all_pending_msgs_enqueue ms (ns : fgraph_node_state) :
    all_pending_msgs (enqueue ms ns) = ms ++ all_pending_msgs ns.
  Proof.
    cbv [all_pending_msgs]. cbn [enqueue gns_queue gns_node_state].
    rewrite <- app_assoc. reflexivity.
  Qed.

  Definition msg_matches (R : rel) (orig : source) '((f, o) : dfact * source) : bool :=
    eqb R (dfact_rel f) && eqb orig o.

  Definition dest_msgs (s1 : fgstate) : list (location * (dfact * source)) :=
    flat_map (fun '(n, ns) => map (fun m => (node_loc n, m)) (all_pending_msgs ns))
             (map.tuples s1.(graph_nodes))
    ++ map (fun m => (output_loc, m)) s1.(graph_output_queue).

  Definition msgs_to_pebbles (R : rel) (orig : source) (dm : list (location * (dfact * source))) : list pebble :=
    map (fun '(loc, (f, _)) => (loc, f)) (filter (fun '(_, m) => msg_matches R orig m) dm).

  Lemma msgs_to_pebbles_app R orig a b :
    msgs_to_pebbles R orig (a ++ b) = msgs_to_pebbles R orig a ++ msgs_to_pebbles R orig b.
  Proof. cbv [msgs_to_pebbles]. rewrite filter_app, map_app. reflexivity. Qed.

  #[export] Instance msgs_to_pebbles_Proper R orig :
    Proper (@Permutation _ ==> @Permutation _) (msgs_to_pebbles R orig).
  Proof. intros a b H. cbv [msgs_to_pebbles]. apply Permutation_map, Permutation_filter, H. Qed.

  Lemma msgs_to_pebbles_forwarded R orig src d L :
    msgs_to_pebbles R orig (map (fun d' => (loc_of_dest d', (d, src))) L)
    = (if (eqb R (dfact_rel d) && eqb orig src)%bool
       then map (fun d' => (loc_of_dest d', d)) L else []).
  Proof.
    cbv [msgs_to_pebbles].
    induction L as [| d' L' IH]; cbn [map filter msg_matches].
    - destr (eqb R (dfact_rel d) && eqb orig src)%bool; reflexivity.
    - destr (eqb R (dfact_rel d) && eqb orig src)%bool; cbn [map]; rewrite IH; reflexivity.
  Qed.

  Lemma msgs_to_pebbles_single R orig loc f o :
    msgs_to_pebbles R orig [(loc, (f, o))]
    = (if (eqb R (dfact_rel f) && eqb orig o)%bool then [(loc, f)] else []).
  Proof.
    cbv [msgs_to_pebbles msg_matches]. cbn [filter map].
    destr (eqb R (dfact_rel f) && eqb orig o)%bool; reflexivity.
  Qed.

  Lemma dest_msgs_map_values'_enqueue (g : node_id -> list (dfact * source)) (s : fgstate) :
    Permutation
      (dest_msgs {| graph_nodes := map_values' (fun n ns => enqueue (g n) ns) s.(graph_nodes);
                    graph_output_queue := s.(graph_output_queue) |})
      (flat_map (fun '(n, _) => map (fun m => (node_loc n, m)) (g n)) (map.tuples s.(graph_nodes))
       ++ dest_msgs s).
  Proof.
    cbv [dest_msgs]. cbn [graph_nodes graph_output_queue].
    rewrite tuples_map_values', flat_map_map, app_assoc.
    apply Permutation_app_tail. apply flat_map_app_perm. intros [n ns]. cbv beta iota.
    rewrite all_pending_msgs_enqueue, map_app. reflexivity.
  Qed.

  Lemma dest_msgs_output_append (s1 s2 : fgstate) oms :
    s1.(graph_nodes) = s2.(graph_nodes) ->
    Permutation s1.(graph_output_queue) (oms ++ s2.(graph_output_queue)) ->
    Permutation (dest_msgs s1) (map (fun m => (output_loc, m)) oms ++ dest_msgs s2).
  Proof.
    intros Hnodes Hperm. cbv [dest_msgs]. rewrite Hnodes.
    etransitivity.
    2: apply Permutation_app_swap_app.
    apply Permutation_app_head.
    rewrite <- map_app. apply Permutation_map. exact Hperm.
  Qed.

  Lemma dest_msgs_get_remove (s : fgstate) n ns :
    map.get s.(graph_nodes) n = Some ns ->
    Permutation
      (dest_msgs s)
      (map (fun m => (node_loc n, m)) (all_pending_msgs ns)
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
      (map (fun m => (node_loc n, m)) new ++ dest_msgs s).
  Proof.
    intros Hget Hperm.
    erewrite dest_msgs_get_remove with (n := n) (ns := v').
    2: { cbn [graph_nodes]. apply map.get_put_same. }
    cbn [graph_nodes graph_output_queue]. rewrite map.remove_put_same.
    rewrite (dest_msgs_get_remove s n v Hget), app_assoc, <- map_app.
    apply Permutation_app_tail. apply Permutation_map. exact Hperm.
  Qed.

  Lemma dest_msgs_put_incl (s : fgstate) n v v' :
    map.get s.(graph_nodes) n = Some v ->
    incl (all_pending_msgs v') (all_pending_msgs v) ->
    incl
      (dest_msgs {| graph_nodes := map.put s.(graph_nodes) n v';
                    graph_output_queue := s.(graph_output_queue) |})
      (dest_msgs s).
  Proof.
    intros Hget Hincl x Hin.
    erewrite dest_msgs_get_remove with (n := n) (ns := v') in Hin.
    2: { cbn [graph_nodes]. apply map.get_put_same. }
    cbn [graph_nodes graph_output_queue] in Hin. rewrite map.remove_put_same in Hin.
    rewrite (dest_msgs_get_remove s n v Hget). apply in_or_app.
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    - left. apply in_map_iff in Hin. destruct Hin as (m & Heq & Hm).
      apply in_map_iff. exists m. split; [ exact Heq | apply Hincl, Hm ].
    - right. exact Hin.
  Qed.

  Definition forwarding_compatible {V} {M : map.map node_id V} (s : M) :=
    forall n, map.get s n <> None <-> map.get fts (node_source n) <> None.

  Context (forwarding_wf :
            forall s ms n, fforwardb s (node_destn n) ms = true -> map.get fts (node_source n) <> None).

  Context (fts_NoDup : forall src mn, NoDup (fforward src mn)).

  Lemma forwarding_graph_edges_from_source src mn :
    Permutation (graph.edges (forwarding_graph mn) (loc_of_source src))
                (map loc_of_dest (fforward src mn)).
  Proof.
    apply NoDup_Permutation.
    - apply graph.edges_NoDup.
    - apply FinFun.Injective_map_NoDup; [ exact loc_of_dest_inj | apply fts_NoDup ].
    - intros w. split.
      + intros Hin. apply forwarding_graph_spec in Hin.
        destruct Hin as (s' & d' & Hind & Hsrc & Hw).
        apply loc_of_source_inj in Hsrc. subst s'. subst w. apply in_map. exact Hind.
      + intros Hin. apply in_map_iff in Hin. destruct Hin as (d' & Hw & Hind).
        apply forwarding_graph_spec. exists src, d'. subst w. auto.
  Qed.

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

  Definition travelling_to (dm : list (location * (dfact * source))) (dest : destn) (queue : list dfact) : Prop :=
    exists queue' : list (dfact * source),
      queue = map fst queue' /\
      Forall (fun '(f, orig) => In dest (nforward orig (dfact_rel f))) queue' /\
      forall R orig,
        In dest (nforward orig R) ->
        Permutation
          (graph_incoming (forwarding_graph (R, orig)) (loc_of_dest dest) (msgs_to_pebbles R orig dm))
          (map fst (filter (msg_matches R orig) queue')).

  Lemma travelling_to_perm dm dm' d q q' :
    Permutation dm dm' ->
    Permutation q q' ->
    travelling_to dm d q ->
    travelling_to dm' d q'.
  Proof.
    intros Hdm Hq (queue' & Hqeq & HF & HP). subst q.
    symmetry in Hq. apply Permutation_map_inv in Hq.
    destruct Hq as (queue'' & Hq'eq & Hqperm).
    exists queue''. split; [exact Hq'eq | split].
    - rewrite <- Hqperm. exact HF.
    - intros R orig Hin. specialize (HP R orig Hin).
      rewrite <- Hdm. etransitivity; [ exact HP | ].
      apply Permutation_map, Permutation_filter, Hqperm.
  Qed.

  #[export] Instance travelling_to_Proper :
    Proper (@Permutation _ ==> eq ==> @Permutation _ ==> iff) travelling_to.
  Proof.
    intros dm dm' Hdm d d' Hd q q' Hq. subst d'. split; intros Ht.
    - eapply travelling_to_perm; [ exact Hdm | exact Hq | exact Ht ].
    - eapply travelling_to_perm; [ symmetry; exact Hdm | symmetry; exact Hq | exact Ht ].
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

  Lemma travelling_to_at loc f orig dest :
    travelling_to [(loc, (f, orig))] dest
      (if (nforwardb orig dest f
           && graph.reachesb (forwarding_graph (dfact_rel f, orig)) loc (loc_of_dest dest))%bool
       then [f] else []).
  Proof.
    destr (nforwardb orig dest f
           && graph.reachesb (forwarding_graph (dfact_rel f, orig)) loc (loc_of_dest dest))%bool.
    - destruct E as [Hroute Hreach].
      exists [(f, orig)]. split; [ reflexivity | split ].
      + constructor; [ exact Hroute | constructor ].
      + intros R o Hprem. rewrite msgs_to_pebbles_single. cbn [filter map msg_matches].
        destr (eqb R (dfact_rel f) && eqb o orig)%bool; [ | reflexivity ].
        destruct E as [-> ->]. cbv [graph_incoming]. cbn [filter].
        destr (graph.reachesb (forwarding_graph (dfact_rel f, orig)) loc (loc_of_dest dest));
          [ reflexivity | contradiction ].
    - exists []. split; [ reflexivity | split; [ constructor | ] ].
      intros R o Hprem. rewrite msgs_to_pebbles_single. cbn [filter map msg_matches].
      destr (eqb R (dfact_rel f) && eqb o orig)%bool; [ | reflexivity ].
      destruct E0 as [-> ->]. cbv [graph_incoming]. cbn [filter].
      destr (graph.reachesb (forwarding_graph (dfact_rel f, orig)) loc (loc_of_dest dest));
        [ | reflexivity ].
      exfalso. destruct E; contradiction.
  Qed.

  Lemma travelling_to_at_dest f orig dest :
    travelling_to [(loc_of_dest dest, (f, orig))] dest (if nforwardb orig dest f then [f] else []).
  Proof.
    pose proof (travelling_to_at (loc_of_dest dest) f orig dest) as H.
    destr (graph.reachesb (forwarding_graph (dfact_rel f, orig)) (loc_of_dest dest) (loc_of_dest dest)).
    - destruct (nforwardb orig dest f); exact H.
    - exfalso. eauto using graph.reaches_self.
  Qed.

  Lemma travelling_to_at_unreached loc f orig dest :
    ~ graph.reaches (forwarding_graph (dfact_rel f, orig)) loc (loc_of_dest dest) ->
    travelling_to [(loc, (f, orig))] dest [].
  Proof.
    intros Hnr. pose proof (travelling_to_at loc f orig dest) as H.
    destr (graph.reachesb (forwarding_graph (dfact_rel f, orig)) loc (loc_of_dest dest));
      [ contradiction | ].
    destruct (nforwardb orig dest f); exact H.
  Qed.

  Lemma travelling_to_nil dest :
    travelling_to [] dest [].
  Proof.
    exists []. split; [ reflexivity | split; [ constructor | ] ].
    intros R orig Hprem. reflexivity.
  Qed.

  Lemma travelling_to_map_unreached L f orig dest :
    Forall (fun d' => ~ graph.reaches (forwarding_graph (dfact_rel f, orig))
                          (loc_of_dest d') (loc_of_dest dest)) L ->
    travelling_to (map (fun d' => (loc_of_dest d', (f, orig))) L) dest [].
  Proof.
    induction L as [| d' L' IH]; cbn [map]; intros HF.
    - apply travelling_to_nil.
    - apply Forall_cons_iff in HF. destruct HF as [Hd' HL'].
      apply (travelling_to_app [_] _ dest [] []).
      + apply travelling_to_at_unreached. exact Hd'.
      + apply IH. exact HL'.
  Qed.

  (* Within a channel (R, orig) every entry's origin is pinned to orig, so a pair is
     determined by its dfact: the sub-multiset cancellation goes through with
     [Permutation_cons_inv], needing no decidable equality on dfact. *)
  Lemma witness_sub_split (Qa Qab : list (dfact * source)) :
    (forall R orig, exists t,
        Permutation (map fst (filter (msg_matches R orig) Qab))
                    (map fst (filter (msg_matches R orig) Qa) ++ t)) ->
    exists Qb, Permutation Qab (Qa ++ Qb).
  Proof.
    revert Qab. induction Qa as [| [f orig] Qa' IH]; intros Qab Hsub.
    - exists Qab. reflexivity.
    - assert (Hmatch : msg_matches (dfact_rel f) orig (f, orig) = true).
      { cbn [msg_matches]. rewrite !eqb_refl_true by typeclasses eauto. reflexivity. }
      assert (Hin : In (f, orig) Qab).
      { destruct (Hsub (dfact_rel f) orig) as [t Ht].
        assert (Hf : In f (map fst (filter (msg_matches (dfact_rel f) orig) Qab))).
        { eapply Permutation_in; [ symmetry; exact Ht | ].
          apply in_or_app. left. cbn [filter]. rewrite Hmatch. cbn [map]. left. reflexivity. }
        apply in_map_iff in Hf. destruct Hf as ((f', o') & Hfst & Hfin). cbn in Hfst. subst f'.
        apply filter_In in Hfin. destruct Hfin as [Hfin Hm].
        cbn [msg_matches] in Hm. apply andb_prop in Hm. destruct Hm as [_ Ho].
        destr (eqb orig o'); [ exact Hfin | discriminate Ho ]. }
      apply in_split in Hin. destruct Hin as (l1 & l2 & Hsplit).
      assert (HQ : Permutation Qab ((f, orig) :: (l1 ++ l2))).
      { subst Qab. symmetry. apply Permutation_middle. }
      destruct (IH (l1 ++ l2)) as (Qb & HQb).
      { intros R o. destruct (Hsub R o) as [t Ht]. exists t.
        assert (Hfilt : Permutation (filter (msg_matches R o) Qab)
                          (filter (msg_matches R o) ((f, orig) :: (l1 ++ l2)))).
        { apply Permutation_filter. exact HQ. }
        cbn [filter] in Hfilt, Ht.
        destruct (msg_matches R o (f, orig)) eqn:M.
        - apply (Permutation_map fst) in Hfilt. cbn [map] in Hfilt, Ht.
          apply (Permutation_cons_inv (a := f)).
          etransitivity; [ symmetry; exact Hfilt | exact Ht ].
        - apply (Permutation_map fst) in Hfilt.
          etransitivity; [ symmetry; exact Hfilt | exact Ht ]. }
      exists Qb. etransitivity; [ exact HQ | ]. apply perm_skip. exact HQb.
  Qed.

  Lemma travelling_to_app_inv a b dest qa qb :
    travelling_to (a ++ b) dest (qa ++ qb) ->
    travelling_to a dest qa ->
    travelling_to b dest qb.
  Proof.
    intros (Qab & HqabE & HFab & HPab) (Qa & HqaE & HFa & HPa).
    assert (Hsub : forall R orig, exists t,
      Permutation (map fst (filter (msg_matches R orig) Qab))
                  (map fst (filter (msg_matches R orig) Qa) ++ t)).
    { intros R orig. destruct (inb dest (nforward orig R)) eqn:Hin.
      - apply inb_true_iff in Hin.
        exists (graph_incoming (forwarding_graph (R, orig)) (loc_of_dest dest)
                  (msgs_to_pebbles R orig b)).
        specialize (HPab R orig Hin). specialize (HPa R orig Hin).
        rewrite msgs_to_pebbles_app, graph_incoming_app in HPab.
        etransitivity; [ symmetry; exact HPab | ].
        apply Permutation_app_tail. exact HPa.
      - assert (Hnr : ~ In dest (nforward orig R)).
        { intro Hc. rewrite <- inb_true_iff in Hc. congruence. }
        assert (Hnil : forall Q, Forall (fun '(f, o) => In dest (nforward o (dfact_rel f))) Q ->
                                 filter (msg_matches R orig) Q = []).
        { intros Q HFQ. erewrite filter_ext_in with (g := fun _ => false); [ apply filter_false | ].
          intros [f o] Hx. rewrite Forall_forall in HFQ. specialize (HFQ _ Hx). cbn beta in HFQ.
          cbn [msg_matches]. destr (eqb R (dfact_rel f) && eqb orig o)%bool; try reflexivity.
          exfalso. destruct E as [-> ->]. apply Hnr. exact HFQ. }
        exists []. rewrite (Hnil Qab HFab), (Hnil Qa HFa). reflexivity. }
    destruct (witness_sub_split Qa Qab Hsub) as (Qb & HQb).
    assert (Hmap : Permutation (map fst Qab) (map fst Qa ++ map fst Qb)).
    { rewrite <- map_app. apply Permutation_map. exact HQb. }
    rewrite <- HqabE, <- HqaE in Hmap. apply Permutation_app_inv_l in Hmap.
    apply (travelling_to_perm b b dest (map fst Qb) qb);
      [ reflexivity | symmetry; exact Hmap | ].
    exists Qb. split; [ reflexivity | split ].
    - eapply Permutation_Forall in HFab; [ | exact HQb ].
      apply Forall_app in HFab. tauto.
    - intros R orig Hin. specialize (HPab R orig Hin). specialize (HPa R orig Hin).
      rewrite msgs_to_pebbles_app, graph_incoming_app in HPab.
      assert (Hfil : Permutation (map fst (filter (msg_matches R orig) Qab))
                       (map fst (filter (msg_matches R orig) Qa)
                        ++ map fst (filter (msg_matches R orig) Qb))).
      { rewrite <- map_app, <- filter_app. apply Permutation_map, Permutation_filter. exact HQb. }
      apply (Permutation_app_inv_l (map fst (filter (msg_matches R orig) Qa))).
      etransitivity; [ apply Permutation_app_tail; symmetry; exact HPa | ].
      etransitivity; [ exact HPab | exact Hfil ].
  Qed.

  (* travelling_to depends on the message list only through the per-channel graph_incoming,
     so a pebble step at a vertex other than dest (unaffected channels unchanged) leaves it
     invariant -- a direct corollary of graph_incoming_pebble_step. *)
  Lemma travelling_to_pebble_step v dm dm' dest queue :
    v <> loc_of_dest dest ->
    (forall R orig,
        (graph.is_locally_tree (forwarding_graph (R, orig)) v /\
         pebble_step (forwarding_graph (R, orig)) v
           (msgs_to_pebbles R orig dm) (msgs_to_pebbles R orig dm'))
        \/ Permutation (msgs_to_pebbles R orig dm) (msgs_to_pebbles R orig dm')) ->
    travelling_to dm dest queue ->
    travelling_to dm' dest queue.
  Proof.
    intros Hne Hstep (queue' & Hq & HF & HP).
    exists queue'. split; [ exact Hq | split; [ exact HF | ] ].
    intros R orig Hin. specialize (HP R orig Hin). specialize (Hstep R orig).
    etransitivity; [ | exact HP ].
    destruct Hstep as [ [Htree Hps] | Hperm ].
    - symmetry. apply graph_incoming_pebble_step with (v := v);
        [ exact Htree | exact Hne | exact Hps ].
    - apply Permutation_graph_incoming. symmetry. exact Hperm.
  Qed.

  Definition forwarding_step (s : source) (f : dfact) (orig : source)
    (dm1 dm2 : list (location * (dfact * source))) : Prop :=
    exists rest,
      Permutation dm1 ((loc_of_source s, (f, orig)) :: rest) /\
      Permutation dm2 (map (fun d' => (loc_of_dest d', (f, orig)))
                         (fforward s (dfact_rel f, orig)) ++ rest).

  Lemma travelling_to_forwarding_step s f orig dm dm' dest queue :
    graph.is_locally_tree (forwarding_graph (dfact_rel f, orig)) (loc_of_source s) ->
    loc_of_source s <> loc_of_dest dest ->
    forwarding_step s f orig dm dm' ->
    travelling_to dm dest queue ->
    travelling_to dm' dest queue.
  Proof.
    intros Htree Hne (rest & Hdm & Hdm') Htr.
    apply (travelling_to_pebble_step (loc_of_source s) dm dm' dest queue Hne); [ | exact Htr ].
    intros R orig'.
    assert (Ha : Permutation (msgs_to_pebbles R orig' dm)
                   (msgs_to_pebbles R orig' [(loc_of_source s, (f, orig))]
                    ++ msgs_to_pebbles R orig' rest)).
    { rewrite <- msgs_to_pebbles_app. apply msgs_to_pebbles_Proper. exact Hdm. }
    assert (Hb : Permutation (msgs_to_pebbles R orig' dm')
                   (msgs_to_pebbles R orig' (map (fun d' => (loc_of_dest d', (f, orig)))
                                              (fforward s (dfact_rel f, orig)))
                    ++ msgs_to_pebbles R orig' rest)).
    { rewrite <- msgs_to_pebbles_app. apply msgs_to_pebbles_Proper. exact Hdm'. }
    rewrite msgs_to_pebbles_forwarded in Hb. rewrite msgs_to_pebbles_single in Ha.
    destr (eqb R (dfact_rel f) && eqb orig' orig)%bool.
    - destruct E as [-> ->].
      left. split; [ exact Htree | ].
      exists (msgs_to_pebbles (dfact_rel f) orig rest), f.
      split.
      + etransitivity; [ exact Ha | ]. reflexivity.
      + etransitivity; [ exact Hb | ]. apply Permutation_app_tail.
        rewrite <- (map_map loc_of_dest (fun v' => (v', f))).
        apply Permutation_map.
        symmetry. apply forwarding_graph_edges_from_source.
    - right. etransitivity; [ exact Ha | ]. symmetry. exact Hb.
  Qed.

  Lemma travelling_to_cons_inv dm dest f orig queue :
    In dest (nforward orig (dfact_rel f)) ->
    travelling_to ((loc_of_dest dest, (f, orig)) :: dm) dest (f :: queue) ->
    travelling_to dm dest queue.
  Proof.
    intros Hin Htr.
    assert (Hhead : travelling_to [(loc_of_dest dest, (f, orig))] dest [f]).
    { pose proof (travelling_to_at_dest f orig dest) as H.
      destr (nforwardb orig dest f); [ exact H | contradiction ]. }
    eapply travelling_to_app_inv; [ | exact Hhead ]. exact Htr.
  Qed.

  Lemma travelling_to_cons_inv_unreached loc f orig dm dest queue :
    ~ graph.reaches (forwarding_graph (dfact_rel f, orig)) loc (loc_of_dest dest) ->
    travelling_to ((loc, (f, orig)) :: dm) dest queue ->
    travelling_to dm dest queue.
  Proof.
    intros Hnr Htr.
    eapply travelling_to_app_inv; [ | apply travelling_to_at_unreached, Hnr ]. exact Htr.
  Qed.

  Lemma travelling_to_single src d dest :
    forwarding_reaches ->
    travelling_to [(loc_of_source src, (d, src))] dest
      (if nforwardb src dest d then [d] else []).
  Proof.
    intros Hreaches. pose proof (travelling_to_at (loc_of_source src) d src dest) as H.
    destr (nforwardb src dest d); [ | exact H ].
    destr (graph.reachesb (forwarding_graph (dfact_rel d, src)) (loc_of_source src) (loc_of_dest dest));
      [ exact H | ].
    exfalso. eauto.
  Qed.

  Lemma travelling_to_deduced n dest outs :
    forwarding_reaches ->
    travelling_to (map (fun x => (node_loc n, (x, node_source n))) outs) dest
      (filter (nforwardb (node_source n) dest) outs).
  Proof.
    intros Hreaches. induction outs as [| x outs' IH].
    - apply travelling_to_nil.
    - cbn [map filter].
      pose proof (travelling_to_single (node_source n) x dest Hreaches) as H1.
      destruct (nforwardb (node_source n) dest x).
      + exact (travelling_to_app [_] _ dest [x] _ H1 IH).
      + exact (travelling_to_app [_] _ dest [] _ H1 IH).
  Qed.

  Lemma travelling_to_in dm dest queue f orig :
    travelling_to dm dest queue ->
    In (loc_of_dest dest, (f, orig)) dm ->
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
      - cbv [msgs_to_pebbles]. apply in_map_iff. exists (loc_of_dest dest, (f, orig)).
        split; [reflexivity|]. apply filter_In. split; [exact Hin|].
        cbn [msg_matches]. rewrite !eqb_refl_true by typeclasses eauto. reflexivity.
      - destr (graph.reachesb (forwarding_graph (dfact_rel f, orig)) (loc_of_dest dest) (loc_of_dest dest));
          [ reflexivity | exfalso; eauto using graph.reaches_self ]. }
    eapply Permutation_in in Hlhs; [| exact HP].
    apply in_map_iff in Hlhs. destruct Hlhs as ((f2, o2) & Hfst & Hin2). simpl in Hfst. subst f2.
    apply filter_In in Hin2. destruct Hin2 as [Hin2 _].
    apply in_map_iff. exists (f, o2). split; [reflexivity | exact Hin2].
  Qed.

  Lemma travelling_to_in_inv dm dest queue f :
    travelling_to dm dest queue ->
    In f queue ->
    exists loc orig,
      In (loc, (f, orig)) dm /\
      graph.reaches (forwarding_graph (dfact_rel f, orig)) loc (loc_of_dest dest) /\
      In dest (nforward orig (dfact_rel f)).
  Proof.
    intros (queue' & Hq & HF & HP) Hin. subst queue.
    apply in_map_iff in Hin. destruct Hin as ((f', orig) & Hfst & Hin). simpl in Hfst. subst f'.
    pose proof (proj1 (Forall_forall _ _) HF _ Hin) as Hprem.
    specialize (HP (dfact_rel f) orig Hprem).
    assert (Hrhs : In f (map fst (filter (msg_matches (dfact_rel f) orig) queue'))).
    { apply in_map_iff. exists (f, orig). split; [ reflexivity | ].
      apply filter_In. split; [ exact Hin | ].
      cbn [msg_matches]. rewrite !eqb_refl_true by typeclasses eauto. reflexivity. }
    eapply Permutation_in in Hrhs; [ | symmetry; exact HP ].
    cbv [graph_incoming] in Hrhs. apply in_map_iff in Hrhs.
    destruct Hrhs as ((loc, f'') & Hsnd & Hpeb). simpl in Hsnd. subst f''.
    apply filter_In in Hpeb. destruct Hpeb as [Hpeb Hreach].
    cbv [msgs_to_pebbles] in Hpeb. apply in_map_iff in Hpeb.
    destruct Hpeb as ((loc', (f'', o)) & Heq & Hdm). fwd.
    apply filter_In in Hdm. destruct Hdm as [Hdm Hmatch].
    cbn [msg_matches] in Hmatch.
    destr (eqb (dfact_rel f) (dfact_rel f) && eqb orig o)%bool; [ | discriminate ].
    destruct E as [_ Eo].
    exists loc, orig. split; [ rewrite Eo; exact Hdm | ].
    split; [ exact Hreach | exact Hprem ].
  Qed.

  Definition queue_at_dest (s : ngstate) (d : destn) :=
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

  Lemma queue_at_dest_get (s : ngstate) n ns :
    map.get s.(graph_nodes) n = Some ns ->
    queue_at_dest s (node_destn n) = ns.(gns_queue).
  Proof. intros Hget. cbn [queue_at_dest]. rewrite Hget. reflexivity. Qed.

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

  Lemma queue_at_dest_put (s : ngstate) n gns' dest :
    Permutation
      (queue_at_dest {| graph_nodes := map.put s.(graph_nodes) n gns';
                           graph_output_queue := s.(graph_output_queue) |} dest)
      (if eqb dest (node_destn n) then gns'.(gns_queue) else queue_at_dest s dest).
  Proof.
    destruct dest as [m | ].
    - destr (eqb (node_destn m) (node_destn n)).
      + cbn [queue_at_dest graph_nodes]. rewrite map.get_put_same.
        cbn [option_map unwrap_or_default unwrap_or gns_queue]. reflexivity.
      + cbn [queue_at_dest graph_nodes]. rewrite map.get_put_diff by congruence.
        reflexivity.
    - destr (eqb output_destn (node_destn n)); [ discriminate | ].
      cbn [queue_at_dest graph_output_queue]. reflexivity.
  Qed.

  Definition to_consume_at (s1 : fgstate) (n : node_id) :=
    unwrap_or_default (option_map (fun ns => ns.(gns_node_state).(fnode_to_consume))
                         (map.get s1.(graph_nodes) n)).

  Definition arrived (s1 : fgstate) (d : destn) :=
    match d with
    | node_destn n => map fst (to_consume_at s1 n)
    | output_destn => []
    end.

  Lemma arrived_get (s : fgstate) n ns :
    map.get s.(graph_nodes) n = Some ns ->
    arrived s (node_destn n) = map fst ns.(gns_node_state).(fnode_to_consume).
  Proof. intros Hget. cbv [arrived to_consume_at]. rewrite Hget. reflexivity. Qed.

  Lemma arrived_put (s : fgstate) n gns' dest :
    arrived {| graph_nodes := map.put s.(graph_nodes) n gns';
               graph_output_queue := s.(graph_output_queue) |} dest
    = if eqb dest (node_destn n)
      then map fst gns'.(gns_node_state).(fnode_to_consume)
      else arrived s dest.
  Proof.
    destruct dest as [m | ].
    - destr (eqb (node_destn m) (node_destn n)).
      + cbv [arrived to_consume_at]. cbn [graph_nodes]. rewrite map.get_put_same. reflexivity.
      + cbv [arrived to_consume_at]. cbn [graph_nodes].
        rewrite map.get_put_diff by congruence. reflexivity.
    - destr (eqb output_destn (node_destn n)); [ discriminate | reflexivity ].
  Qed.

  Lemma arrived_put_unchanged (s : fgstate) n ns gns' dest :
    map.get s.(graph_nodes) n = Some ns ->
    gns'.(gns_node_state).(fnode_to_consume) = ns.(gns_node_state).(fnode_to_consume) ->
    arrived {| graph_nodes := map.put s.(graph_nodes) n gns';
               graph_output_queue := s.(graph_output_queue) |} dest
    = arrived s dest.
  Proof.
    intros Hget Hto. rewrite arrived_put. destr (eqb dest (node_destn n)); [ | reflexivity ].
    rewrite Hto. symmetry. apply arrived_get, Hget.
  Qed.

  Lemma arrived_forward_to keep msgs (s : fgstate) dest :
    arrived (forward_to keep msgs s) dest = arrived s dest.
  Proof.
    destruct dest as [n | ]; [ | reflexivity ].
    cbv [arrived to_consume_at]. cbn [forward_to graph_nodes]. rewrite get_map_values'.
    destruct (map.get s.(graph_nodes) n); reflexivity.
  Qed.

  Definition wf_queues (s1 : fgstate) :=
    forall f orig,
      In (f, orig) s1.(graph_output_queue) ->
      In output_destn (nforward orig (dfact_rel f)).

  Definition dm_reachable (dm : list (location * (dfact * source))) :=
    forall loc f orig,
      In (loc, (f, orig)) dm ->
      graph.reaches (forwarding_graph (dfact_rel f, orig)) (loc_of_source orig) loc.

  Lemma dm_reachable_app dm1 dm2 :
    dm_reachable dm1 -> dm_reachable dm2 -> dm_reachable (dm1 ++ dm2).
  Proof.
    intros H1 H2 loc f orig Hin. apply in_app_or in Hin. destruct Hin; auto.
  Qed.

  Lemma dm_reachable_incl dm dm' :
    incl dm' dm -> dm_reachable dm -> dm_reachable dm'.
  Proof. intros Hincl Hdm loc f orig Hin. apply Hdm, Hincl, Hin. Qed.

  Lemma dm_reachable_perm dm dm' :
    Permutation dm dm' -> dm_reachable dm' -> dm_reachable dm.
  Proof.
    intros Hp Hdm loc f orig Hin. apply Hdm. eapply Permutation_in; [ exact Hp | exact Hin ].
  Qed.

  Lemma dm_reachable_forwarded src f orig :
    graph.reaches (forwarding_graph (dfact_rel f, orig)) (loc_of_source orig) (loc_of_source src) ->
    dm_reachable (map (fun d' => (loc_of_dest d', (f, orig))) (fforward src (dfact_rel f, orig))).
  Proof.
    intros Hre loc f' orig' Hin. apply in_map_iff in Hin.
    destruct Hin as (d' & Heq & Hind). injection Heq as <- <- <-.
    eapply graph.reaches_step; [ exact Hre | ].
    apply forwarding_graph_spec. exists src, d'. auto.
  Qed.

  Lemma dm_reachable_deduced n outs :
    dm_reachable (map (fun m => (node_loc n, m)) (map (fun f => (f, node_source n)) outs)).
  Proof.
    rewrite map_map. intros loc f orig Hin. apply in_map_iff in Hin.
    destruct Hin as (x & Heq & _). injection Heq as <- <- <-. apply graph.reaches_self.
  Qed.

  Definition msgs_reachable (s1 : fgstate) := dm_reachable (dest_msgs s1).

  (* TODO better name *)
  Definition delivered_to (s1 : fgstate) (s2 : ngstate) (dest : destn) :=
    exists queue,
      Permutation (queue_at_dest s2 dest) (arrived s1 dest ++ queue) /\
      travelling_to (dest_msgs s1) dest queue.

  Lemma delivered_to_arrived_incl (s1 : fgstate) (s2 : ngstate) dest :
    delivered_to s1 s2 dest ->
    incl (arrived s1 dest) (queue_at_dest s2 dest).
  Proof.
    intros (queue & Hperm & _) x Hx. eapply Permutation_in; [ symmetry; exact Hperm | ].
    apply in_or_app. auto.
  Qed.

  Definition forwarding_R
    (s1 : fgstate) (t1 : list fnIO_event)
    (s2 : ngstate) (t2 : list nIO_event) : Prop :=
    flat_map inputs_of t1 = flat_map inputs_of t2 /\
      flat_map outputs_of t1 = flat_map outputs_of t2 /\
      forwarding_compatible s1.(graph_nodes) /\
      wf_queues s1 /\
      Forall2_map (fun _ fgns ngns =>
                     fgns.(gns_node_state).(fnode_node) = ngns.(gns_node_state))
        s1.(graph_nodes) s2.(graph_nodes) /\
      msgs_reachable s1 /\
      (forall dest, valid_dest dest -> delivered_to s1 s2 dest).

  Lemma in_output_dest_msgs (s : fgstate) f orig :
    In (f, orig) s.(graph_output_queue) ->
    In (output_loc, (f, orig)) (dest_msgs s).
  Proof.
    intros Hin. cbv [dest_msgs]. apply in_or_app. right.
    apply in_map_iff. exists (f, orig). split; [reflexivity | exact Hin].
  Qed.

  Lemma in_node_dest_msgs (s : fgstate) n ns m :
    map.get s.(graph_nodes) n = Some ns ->
    In m (all_pending_msgs ns) ->
    In (node_loc n, m) (dest_msgs s).
  Proof.
    intros Hget Hin. cbv [dest_msgs]. apply in_or_app. left.
    apply in_flat_map. exists (n, ns). split; [ apply map.tuples_spec; exact Hget | ].
    apply in_map_iff. exists m. split; [reflexivity | exact Hin].
  Qed.

  Lemma forwarding_R_output_incl_rev s1 t1 s2 t2 :
    forwarding_R s1 t1 s2 t2 ->
    incl (map fst s1.(graph_output_queue)) s2.(graph_output_queue).
  Proof.
    intros HR. cbv [forwarding_R delivered_to] in HR. fwd.
    specialize (HRp6 output_destn I). fwd. cbn [arrived app] in HRp6p0.
    intros f Hf. apply in_map_iff in Hf. destruct Hf as ((f', orig) & Heq & Hin).
    simpl in Heq. subst f'.
    eapply Permutation_in; [ symmetry; exact HRp6p0 | ].
    apply (travelling_to_in _ output_destn _ f orig HRp6p1).
    - apply in_output_dest_msgs. exact Hin.
    - eapply HRp3. exact Hin.
  Qed.

  Lemma wf_queues_incl (sa sb : fgstate) :
    incl sa.(graph_output_queue) sb.(graph_output_queue) ->
    wf_queues sb ->
    wf_queues sa.
  Proof.
    intros Hincl Hsb f orig Hin. apply Hsb. apply Hincl. exact Hin.
  Qed.

  Lemma travelling_to_forwarded src d dest :
    forwarding_reaches -> forwarding_tree ->
    loc_of_source src <> loc_of_dest dest ->
    travelling_to (map (fun d' => (loc_of_dest d', (d, src))) (fforward src (dfact_rel d, src))) dest
      (filter (nforwardb src dest) [d]).
  Proof.
    intros Hreaches Htree Hne.
    change (filter (nforwardb src dest) [d]) with (if nforwardb src dest d then [d] else []).
    eapply (travelling_to_forwarding_step src d src [(loc_of_source src, (d, src))]);
      [ apply Htree | exact Hne | | apply travelling_to_single; assumption ].
    exists []. split; [ reflexivity | rewrite app_nil_r; reflexivity ].
  Qed.

  Lemma filter_fforwardb_single src dst d orig :
    filter (fforwardb src dst) [(d, orig)]
    = if inb dst (fforward src (dfact_rel d, orig)) then [(d, orig)] else [].
  Proof.
    cbn [filter fforwardb].
    destruct (inb dst (fforward src (dfact_rel d, orig))); reflexivity.
  Qed.

  Lemma in_map_filter_fforwardb src dst d orig (loc : location) x :
    In x (map (fun m => (loc, m)) (filter (fforwardb src dst) [(d, orig)])) <->
    x = (loc, (d, orig)) /\ In dst (fforward src (dfact_rel d, orig)).
  Proof.
    rewrite filter_fforwardb_single.
    destruct (inb dst (fforward src (dfact_rel d, orig))) eqn:Hb; cbn [map In].
    - rewrite inb_true_iff in Hb. split.
      + intros [Heq | []]. auto.
      + intros [-> _]. auto.
    - split.
      + intros [].
      + intros [_ Hin]. rewrite <- inb_true_iff in Hin. congruence.
  Qed.

  Lemma dest_msgs_forward_to src d orig (s : fgstate) :
    forwarding_compatible s.(graph_nodes) ->
    Permutation
      (dest_msgs (forward_to (fforwardb src) [(d, orig)] s))
      (map (fun d' => (loc_of_dest d', (d, orig))) (fforward src (dfact_rel d, orig)) ++ dest_msgs s).
  Proof.
    intros Hcompat.
    transitivity
      (map (fun m => (output_loc, m)) (filter (fforwardb src output_destn) [(d, orig)])
       ++ (flat_map (fun '(n, _) => map (fun m => (node_loc n, m))
                      (filter (fforwardb src (node_destn n)) [(d, orig)])) (map.tuples s.(graph_nodes))
           ++ dest_msgs s)).
    { etransitivity.
      - apply dest_msgs_output_append with
          (oms := filter (fforwardb src output_destn) [(d, orig)])
          (s2 := {| graph_nodes := map_values' (fun n ns =>
                      enqueue (filter (fforwardb src (node_destn n)) [(d, orig)]) ns) s.(graph_nodes);
                    graph_output_queue := s.(graph_output_queue) |}).
        + cbn [forward_to graph_nodes]. reflexivity.
        + cbn [forward_to graph_output_queue]. reflexivity.
      - apply Permutation_app_head.
        apply (dest_msgs_map_values'_enqueue
                 (fun n => filter (fforwardb src (node_destn n)) [(d, orig)]) s). }
    rewrite app_assoc. apply Permutation_app_tail.
    apply NoDup_Permutation.
    - apply NoDup_app.
      + rewrite filter_fforwardb_single.
        destruct (inb output_destn (fforward src (dfact_rel d, orig)));
          repeat constructor; simpl; tauto.
      + apply List.NoDup_flat_map.
        * apply map.tuples_NoDup.
        * intros [n ns] _. rewrite filter_fforwardb_single.
          destruct (inb (node_destn n) (fforward src (dfact_rel d, orig)));
            repeat constructor; simpl; tauto.
        * intros [n1 ns1] [n2 ns2] b Hin1 Hin2 Hb1 Hb2.
          apply in_map_filter_fforwardb in Hb1, Hb2.
          destruct Hb1 as [Hb1 _]. destruct Hb2 as [Hb2 _]. subst b.
          injection Hb2 as Hn. subst n2.
          rewrite map.tuples_spec in Hin1, Hin2. congruence.
      + intros x Hout Hnode.
        apply in_map_filter_fforwardb in Hout. destruct Hout as [-> _].
        apply in_flat_map in Hnode. destruct Hnode as [[n ns] [_ Hnode]].
        apply in_map_filter_fforwardb in Hnode. destruct Hnode as [Heq _].
        discriminate Heq.
    - apply FinFun.Injective_map_NoDup; [ | apply fts_NoDup ].
      intros a b Hab. apply loc_of_dest_inj. congruence.
    - intros x. rewrite in_app_iff. split.
      + intros [Hout | Hnode].
        * apply in_map_filter_fforwardb in Hout. destruct Hout as [-> Hind].
          apply in_map_iff. exists output_destn. auto.
        * apply in_flat_map in Hnode. destruct Hnode as [[n ns] [_ Hnode]].
          apply in_map_filter_fforwardb in Hnode. destruct Hnode as [-> Hind].
          apply in_map_iff. exists (node_destn n). auto.
      + intros Hin. apply in_map_iff in Hin. destruct Hin as [d' [Heq Hind]].
        subst x. destruct d' as [n | ].
        * right. apply in_flat_map.
          destruct (map.get s.(graph_nodes) n) as [ns | ] eqn:Hget.
          2: { exfalso.
               assert (Hfts : map.get fts (node_source n) <> None).
               { apply (forwarding_wf src (d, orig) n). cbv [fforwardb].
                 apply inb_true_iff. exact Hind. }
               exact (proj2 (Hcompat n) Hfts Hget). }
          exists (n, ns). split; [ apply map.tuples_spec; exact Hget | ].
          apply in_map_filter_fforwardb. auto.
        * left. apply in_map_filter_fforwardb. auto.
  Qed.

  Lemma msgs_reachable_pending (s : fgstate) n ns q1 f orig q2 :
    msgs_reachable s ->
    map.get s.(graph_nodes) n = Some ns ->
    ns.(gns_node_state).(fnode_pending) = q1 ++ (f, orig) :: q2 ->
    graph.reaches (forwarding_graph (dfact_rel f, orig)) (loc_of_source orig) (node_loc n).
  Proof.
    intros Hmr Hget Hpend. apply Hmr. eapply in_node_dest_msgs; [ exact Hget | ].
    cbv [all_pending_msgs]. apply in_or_app. right. rewrite Hpend.
    apply in_or_app. right. left. reflexivity.
  Qed.

  Lemma msgs_reachable_forward_to src f orig (s : fgstate) :
    forwarding_compatible s.(graph_nodes) ->
    graph.reaches (forwarding_graph (dfact_rel f, orig)) (loc_of_source orig) (loc_of_source src) ->
    msgs_reachable s ->
    msgs_reachable (forward_to (fforwardb src) [(f, orig)] s).
  Proof.
    intros Hcompat Hre Hmr. unfold msgs_reachable in *.
    eapply dm_reachable_perm; [ apply dest_msgs_forward_to, Hcompat | ].
    apply dm_reachable_app; [ apply dm_reachable_forwarded, Hre | exact Hmr ].
  Qed.

  Lemma msgs_reachable_put_incl (s : fgstate) n v v' :
    map.get s.(graph_nodes) n = Some v ->
    incl (all_pending_msgs v') (all_pending_msgs v) ->
    msgs_reachable s ->
    msgs_reachable {| graph_nodes := map.put s.(graph_nodes) n v';
                      graph_output_queue := s.(graph_output_queue) |}.
  Proof.
    intros Hget Hincl Hmr. unfold msgs_reachable in *.
    eapply dm_reachable_incl.
    - eapply dest_msgs_put_incl; [ exact Hget | exact Hincl ].
    - exact Hmr.
  Qed.

  Lemma all_pending_msgs_dequeue (ns v' : fgraph_node_state) q1 f orig q2 :
    v'.(gns_queue) = ns.(gns_queue) ->
    v'.(gns_node_state).(fnode_pending) = q1 ++ q2 ->
    ns.(gns_node_state).(fnode_pending) = q1 ++ (f, orig) :: q2 ->
    Permutation (all_pending_msgs ns) ((f, orig) :: all_pending_msgs v').
  Proof.
    intros Hq Hv' Hns. cbv [all_pending_msgs]. rewrite Hq, Hv', Hns, !app_assoc.
    symmetry. apply Permutation_middle.
  Qed.

  Lemma incl_all_pending_dequeue (ns v' : fgraph_node_state) q1 f orig q2 :
    v'.(gns_queue) = ns.(gns_queue) ->
    v'.(gns_node_state).(fnode_pending) = q1 ++ q2 ->
    ns.(gns_node_state).(fnode_pending) = q1 ++ (f, orig) :: q2 ->
    incl (all_pending_msgs v') (all_pending_msgs ns).
  Proof.
    intros Hq Hv' Hns x Hx. eapply Permutation_in.
    - symmetry. eapply all_pending_msgs_dequeue; eassumption.
    - right. exact Hx.
  Qed.

  Lemma dest_msgs_dequeue (s : fgstate) n ns v' f orig :
    map.get s.(graph_nodes) n = Some ns ->
    Permutation (all_pending_msgs ns) ((f, orig) :: all_pending_msgs v') ->
    Permutation (dest_msgs s)
      ((node_loc n, (f, orig))
       :: dest_msgs {| graph_nodes := map.put s.(graph_nodes) n v';
                       graph_output_queue := s.(graph_output_queue) |}).
  Proof.
    intros Hget Hperm.
    etransitivity; [ apply (dest_msgs_get_remove s n ns Hget) | ].
    rewrite (Permutation_map (fun m => (node_loc n, m)) Hperm).
    cbn [map]. rewrite <- app_comm_cons. apply perm_skip.
    symmetry. etransitivity.
    { apply dest_msgs_get_remove. cbn [graph_nodes]. apply map.get_put_same. }
    cbn [graph_nodes graph_output_queue]. rewrite map.remove_put_same. reflexivity.
  Qed.

  Lemma travelling_to_dequeue (s : fgstate) n ns v' f orig dest queue :
    forwarding_tree ->
    forwarding_compatible s.(graph_nodes) ->
    msgs_reachable s ->
    map.get s.(graph_nodes) n = Some ns ->
    Permutation (all_pending_msgs ns) ((f, orig) :: all_pending_msgs v') ->
    dest <> node_destn n ->
    travelling_to (dest_msgs s) dest queue ->
    travelling_to
      (dest_msgs (forward_to (fforwardb (node_source n)) [(f, orig)]
                    {| graph_nodes := map.put s.(graph_nodes) n v';
                       graph_output_queue := s.(graph_output_queue) |}))
      dest queue.
  Proof.
    intros Htree Hcompat Hmr Hget Hperm Hne Htr.
    eapply travelling_to_forwarding_step with (s := node_source n) (f := f) (orig := orig).
    - eapply is_locally_tree_reaches.
      + apply Hmr. eapply in_node_dest_msgs; [ exact Hget | ].
        rewrite Hperm. left. reflexivity.
      + apply Htree.
    - destruct dest; cbn [loc_of_source loc_of_dest]; congruence.
    - eexists. split.
      + cbn [loc_of_source]. eapply dest_msgs_dequeue; eassumption.
      + apply dest_msgs_forward_to.
        eapply forwarding_compatible_same_domain; [ exact Hcompat | ].
        cbn [graph_nodes]. eapply same_domain_put_r. exact Hget.
    - exact Htr.
  Qed.

  Lemma forwarding_R_silent_step s1 t1 s2 t2 e s1' :
    forwarding_reaches ->
    forwarding_tree ->
    no_extra_outputs ->
    forwarding_R s1 t1 s2 t2 ->
    fgraph_step s1 e s1' ->
    silent_event e ->
    forwarding_R s1' (e :: t1) s2 t2.
  Proof.
    intros Hreaches Htree Hno H Hstep Hsilent.
    cbv [fgraph_step] in Hstep. fwd. invert Hstepp1.
    - destruct e; simpl in Hstepp0; fwd; [ destruct Hsilent | congruence ].
    - destruct e; simpl in Hstepp0; congruence || fwd. invert H1.
      + destruct Hsilent.
      + cbv [forwarding_R] in H. fwd.
        pose proof @Forall2_map_get_l as Hget. especialize Hget; try eassumption. fwd.
        cbv [forwarding_R]. simpl.
        split; [assumption|]. split; [assumption|].
        split.
        { eapply forwarding_compatible_same_domain; [exact Hp2|].
          eapply same_domain_trans;
            [ eapply same_domain_put_r; exact H0 | apply same_domain_map_values' ]. }
        split.
        { intros f' orig' Hin.
          cbn [forward_to graph_output_queue] in Hin. apply in_app_or in Hin.
          destruct Hin as [Hin | Hin]; [ | exact (Hp3 _ _ Hin) ].
          apply filter_In in Hin. destruct Hin as [Hin Hkeep].
          destruct Hin as [Heq | []]. injection Heq as <- <-.
          apply inb_true_iff in Hkeep. apply Hno.
          eapply graph.reaches_step.
          - eapply msgs_reachable_pending; [ exact Hp5 | exact H0 | exact H6 ].
          - apply forwarding_graph_spec. exists (node_source n), output_destn.
            split; [ exact Hkeep | split; reflexivity ]. }
        split.
        { apply Forall2_map_map_values'_l. simpl.
          eapply Forall2_map_put_l; [|eassumption|].
          2: { simpl. assumption. }
          eapply Forall2_map_impl; [eassumption|]. simpl. auto. }
        split.
        { apply msgs_reachable_forward_to.
          - eapply forwarding_compatible_same_domain; [exact Hp2|].
            cbn [graph_nodes]. eapply same_domain_put_r. exact H0.
          - eapply msgs_reachable_pending; [ exact Hp5 | exact H0 | exact H6 ].
          - eapply msgs_reachable_put_incl.
            + exact H0.
            + eapply incl_all_pending_dequeue; [ reflexivity | reflexivity | exact H6 ].
            + exact Hp5. }
        intros dest Hdest. specialize (Hp6 dest Hdest).
        destruct Hp6 as (Q & HQ & Htr). cbv [delivered_to].
        setoid_rewrite arrived_forward_to. setoid_rewrite arrived_put.
        destr (eqb dest (node_destn n)).
        2: { exists Q. split; [ exact HQ | ].
             eapply travelling_to_dequeue; try eassumption.
             eapply all_pending_msgs_dequeue; [ reflexivity | reflexivity | exact H6 ]. }
        setoid_rewrite dest_msgs_forward_to.
        2: { eapply forwarding_compatible_same_domain; [ exact Hp2 | ].
             cbn [graph_nodes]. eapply same_domain_put_r. exact H0. }
        destr (inb (node_destn n) (nforward orig (dfact_rel f))).
        -- eapply travelling_to_in in Htr as Hf.
           2: { eapply in_node_dest_msgs; [ exact H0 | ].
                cbv [all_pending_msgs]. apply in_or_app. right. rewrite H6.
                apply in_or_app. right. left. reflexivity. }
           2: { exact E. }
           apply in_split in Hf. destruct Hf as (Qa & Qb & ->).
           exists (Qa ++ Qb). split.
           { rewrite HQ. erewrite arrived_get by exact H0.
             cbn [map fst fnode_to_consume gns_node_state app].
             rewrite !app_assoc. symmetry. apply Permutation_middle. }
           apply travelling_to_app with (queueA := []).
           { apply travelling_to_map_unreached. apply Forall_forall. intros d' Hd'.
             eapply is_locally_tree_no_return.
             - apply Htree.
             - eapply msgs_reachable_pending; [ exact Hp5 | exact H0 | exact H6 ].
             - apply forwarding_graph_spec. exists (node_source n), d'.
               split; [ exact Hd' | split; reflexivity ]. }
           eapply travelling_to_app_inv with (qa := [f]).
           2: { pose proof (travelling_to_at_dest f orig (node_destn n)) as Hat.
                destr (nforwardb orig (node_destn n) f); [ exact Hat | contradiction ]. }
           rewrite <- Permutation_middle in Htr.
           eapply travelling_to_perm; [ | reflexivity | exact Htr ].
           eapply dest_msgs_dequeue; [ exact H0 | ].
           eapply all_pending_msgs_dequeue; [ reflexivity | reflexivity | exact H6 ].
        -- exists Q. split.
           { rewrite HQ. erewrite arrived_get by exact H0. reflexivity. }
           apply travelling_to_app with (queueA := []).
           { apply travelling_to_map_unreached. apply Forall_forall. intros d' Hd'.
             eapply is_locally_tree_no_return.
             - apply Htree.
             - eapply msgs_reachable_pending; [ exact Hp5 | exact H0 | exact H6 ].
             - apply forwarding_graph_spec. exists (node_source n), d'.
               split; [ exact Hd' | split; reflexivity ]. }
           eapply travelling_to_app_inv with (qa := []).
           2: { pose proof (travelling_to_at_dest f orig (node_destn n)) as Hat.
                destr (nforwardb orig (node_destn n) f); [ contradiction | exact Hat ]. }
           eapply travelling_to_perm; [ | reflexivity | exact Htr ].
           eapply dest_msgs_dequeue; [ exact H0 | ].
           eapply all_pending_msgs_dequeue; [ reflexivity | reflexivity | exact H6 ].
      + destruct Hsilent.
    - destruct e; simpl in Hstepp0; congruence || fwd. invert H1.
      cbv [forwarding_R] in *. simpl. fwd.
      split; [assumption|]. split; [assumption|]. split.
      { eapply forwarding_compatible_same_domain; [eassumption|].
        eapply same_domain_put_r. exact H0. }
      split.
      { assumption. }
      split.
      { pose proof @Forall2_map_get_l as H'. especialize H'; eauto. fwd.
        eapply Forall2_map_put_l; try eassumption.
        eapply Forall2_map_impl; [eassumption|]. auto. }
      split.
      { unfold msgs_reachable.
        eapply dm_reachable_perm.
        { eapply dest_msgs_put with (new := []).
          - eassumption.
          - cbv [all_pending_msgs]. simpl. rewrite H2. rewrite <- !app_assoc.
            apply Permutation_app_head. symmetry. apply Permutation_middle. }
        simpl. assumption. }
      intros dest Hdest. specialize (Hp6 dest Hdest).
      destruct Hp6 as (Q & HQ & Htr). cbv [delivered_to]. exists Q. split.
      { erewrite arrived_put_unchanged by (eassumption || reflexivity). exact HQ. }
      rewrite dest_msgs_put with (new := []).
      2: eassumption.
      2: { cbv [all_pending_msgs]. simpl. rewrite H2. rewrite <- !app_assoc.
           apply Permutation_app_head. symmetry. apply Permutation_middle. }
      simpl. exact Htr.
    - destruct e; simpl in Hstepp0; congruence || fwd. destruct Hsilent.
  Qed.

  Lemma in_dest_msgs_inv (s : fgstate) loc m :
    In (loc, m) (dest_msgs s) ->
    (exists n ns, loc = node_loc n /\ map.get s.(graph_nodes) n = Some ns
                  /\ In m (all_pending_msgs ns))
    \/ (loc = output_loc /\ In m s.(graph_output_queue)).
  Proof.
    cbv [dest_msgs]. intros Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    - left. apply in_flat_map in Hin. destruct Hin as ((n, ns) & Htup & Hin).
      apply in_map_iff in Hin. destruct Hin as (m' & Heq & Hm'). fwd.
      exists n, ns. split; [ reflexivity | ].
      split; [ apply map.tuples_spec, Htup | exact Hm' ].
    - right. apply in_map_iff in Hin. destruct Hin as (m' & Heq & Hm'). fwd.
      split; [ reflexivity | exact Hm' ].
  Qed.

  Lemma fgraph_to_pending (s : fgstate) n ns m :
    map.get s.(graph_nodes) n = Some ns ->
    In m (all_pending_msgs ns) ->
    exists s' t ns',
      star fgraph_step s t s' /\
      Forall silent_event t /\
      map.get s'.(graph_nodes) n = Some ns' /\
      In m ns'.(gns_node_state).(fnode_pending).
  Proof.
    intros Hget Hin. cbv [all_pending_msgs] in Hin. apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    2: { exists s, [], ns. split; [ apply star_refl | ].
         split; [ constructor | split; [ exact Hget | exact Hin ] ]. }
    apply in_split in Hin. destruct Hin as (ms1 & ms2 & Hms).
    eexists _, [O_event (receive n m) []], _. split.
    { apply star_one. cbv [fgraph_step]. eexists. split.
      { cbn [corresp]. exists []. split; reflexivity. }
      eapply gstep_receive; [ exact Hget | apply fnode_input | exact Hms ]. }
    split; [ repeat constructor | ].
    cbn [graph_nodes]. rewrite map.get_put_same.
    split; [ reflexivity | ]. cbn [gns_node_state fnode_pending]. left. reflexivity.
  Qed.

  Lemma in_forward_to_dest_msgs keep msgs (s : fgstate) m msg :
    map.get s.(graph_nodes) m <> None ->
    In msg (filter (keep (node_destn m)) msgs) ->
    In (node_loc m, msg) (dest_msgs (forward_to keep msgs s)).
  Proof.
    intros Hm Hin. destruct (map.get s.(graph_nodes) m) as [ms|] eqn:Hget; [ | congruence ].
    eapply in_node_dest_msgs.
    - cbn [forward_to graph_nodes]. rewrite get_map_values', Hget. reflexivity.
    - rewrite all_pending_msgs_enqueue. apply in_or_app. left. exact Hin.
  Qed.

  Lemma in_forward_to_output keep msgs (s : fgstate) msg :
    In msg (filter (keep output_destn) msgs) ->
    In (output_loc, msg) (dest_msgs (forward_to keep msgs s)).
  Proof.
    intros Hin. destruct msg as (f, orig). apply in_output_dest_msgs.
    cbn [forward_to graph_output_queue]. apply in_or_app. left. exact Hin.
  Qed.

  Lemma fgraph_route_step (s : fgstate) n ns f orig q1 q2 :
    map.get s.(graph_nodes) n = Some ns ->
    ns.(gns_node_state).(fnode_pending) = q1 ++ (f, orig) :: q2 ->
    fgraph_step s (O_event (run n (forward_label f)) [])
      (forward_to (fforwardb (node_source n)) [(f, orig)]
         {| graph_nodes :=
              map.put s.(graph_nodes) n
                {| gns_node_state :=
                     {| fnode_node := ns.(gns_node_state).(fnode_node);
                        fnode_pending := q1 ++ q2;
                        fnode_to_consume :=
                          if (fprog_at n).(fnode_keep) f orig
                          then (f, orig) :: ns.(gns_node_state).(fnode_to_consume)
                          else ns.(gns_node_state).(fnode_to_consume) |};
                   gns_trace := O_event (forward_label f) [(f, orig)] :: ns.(gns_trace);
                   gns_queue := ns.(gns_queue) |};
            graph_output_queue := s.(graph_output_queue) |}).
  Proof.
    intros Hget Hq. cbv [fgraph_step]. eexists. split.
    { cbn [corresp]. exists []. split; reflexivity. }
    eapply gstep_run; [ exact Hget | ]. apply fnode_route. exact Hq.
  Qed.

  Lemma fgraph_route_to (s : fgstate) n ns f orig d :
    forwarding_compatible s.(graph_nodes) ->
    map.get s.(graph_nodes) n = Some ns ->
    In (f, orig) ns.(gns_node_state).(fnode_pending) ->
    In d (fforward (node_source n) (dfact_rel f, orig)) ->
    exists s',
      fgraph_step s (O_event (run n (forward_label f)) []) s' /\
      In (loc_of_dest d, (f, orig)) (dest_msgs s').
  Proof.
    intros Hcompat Hget Hin Hd.
    apply in_split in Hin. destruct Hin as (q1 & q2 & Hq).
    eexists. split; [ eapply fgraph_route_step; eassumption | ].
    assert (Hkeep : filter (fforwardb (node_source n) d) [(f, orig)] = [(f, orig)]).
    { rewrite filter_fforwardb_single. destr (inb d (fforward (node_source n) (dfact_rel f, orig)));
        [ reflexivity | contradiction ]. }
    destruct d as [m | ].
    - apply in_forward_to_dest_msgs; [ | rewrite Hkeep; left; reflexivity ].
      cbn [graph_nodes]. destr (eqb n m).
      { rewrite map.get_put_same. congruence. }
      rewrite map.get_put_diff by (symmetry; exact E).
      apply (proj2 (Hcompat m)). eapply (forwarding_wf (node_source n) (f, orig)).
      cbn [fforwardb]. apply (proj2 (inb_true_iff _ _)). exact Hd.
    - apply in_forward_to_output. rewrite Hkeep. left. reflexivity.
  Qed.

  Lemma fgraph_route_keeps (s : fgstate) n ns f orig :
    map.get s.(graph_nodes) n = Some ns ->
    In (f, orig) ns.(gns_node_state).(fnode_pending) ->
    In (node_destn n) (nforward orig (dfact_rel f)) ->
    exists s',
      fgraph_step s (O_event (run n (forward_label f)) []) s' /\
      In (f, orig) (to_consume_at s' n).
  Proof.
    intros Hget Hin Hkeep.
    apply in_split in Hin. destruct Hin as (q1 & q2 & Hq).
    eexists. split; [ eapply fgraph_route_step; eassumption | ].
    cbv [to_consume_at]. cbn [forward_to graph_nodes]. rewrite get_map_values'.
    rewrite map.get_put_same.
    cbn [option_map unwrap_or_default unwrap_or enqueue gns_node_state fnode_to_consume fprog_at fnode_keep].
    destr (inb (node_destn n) (nforward orig (dfact_rel f))); [ | contradiction ].
    left. reflexivity.
  Qed.

  Lemma forwarding_R_silent_star s1 t1 s2 t2 t1' s1' :
    forwarding_reaches ->
    forwarding_tree ->
    no_extra_outputs ->
    forwarding_R s1 t1 s2 t2 ->
    star fgraph_step s1 t1' s1' ->
    Forall silent_event t1' ->
    forwarding_R s1' (t1' ++ t1) s2 t2.
  Proof.
    intros Hreaches Htree Hno HR Hstar. induction Hstar as [ | t0 sa e sb Hstar IH Hstep ].
    - intros _. exact HR.
    - intros Hsil. apply Forall_cons_iff in Hsil. destruct Hsil as [Hsile Hsil0].
      eapply forwarding_R_silent_step; try eassumption. apply IH, Hsil0.
  Qed.

  Lemma fgraph_hop (s1 : fgstate) t1 s2 t2 f orig loc next :
    forwarding_reaches ->
    forwarding_tree ->
    no_extra_outputs ->
    forwarding_R s1 t1 s2 t2 ->
    In (loc, (f, orig)) (dest_msgs s1) ->
    graph.edge (forwarding_graph (dfact_rel f, orig)) loc next ->
    exists s1' t1',
      star fgraph_step s1 t1' s1' /\
      Forall silent_event t1' /\
      In (next, (f, orig)) (dest_msgs s1').
  Proof.
    intros Hreaches Htree Hno HR Hin Hedge.
    apply forwarding_graph_spec in Hedge. destruct Hedge as (src & d & Hd & Hsrc & Hnext).
    apply in_dest_msgs_inv in Hin.
    destruct Hin as [(n & ns & Hloc & Hget & Hpend) | (Hloc & Hout)].
    2: { subst loc. destruct src; discriminate Hsrc. }
    subst loc. assert (src = node_source n) by (destruct src; simpl in Hsrc; congruence).
    subst src.
    destruct (fgraph_to_pending s1 n ns (f, orig) Hget Hpend)
      as (sa & ta & ns' & Hstara & Hsila & Hgeta & Hpenda).
    pose proof (forwarding_R_silent_star _ _ _ _ _ _ Hreaches Htree Hno HR Hstara Hsila) as HRa.
    cbv [forwarding_R] in HRa. fwd.
    destruct (fgraph_route_to sa n ns' f orig d HRap2 Hgeta Hpenda Hd) as (sb & Hstep & Hinb).
    exists sb, (O_event (run n (forward_label f)) [] :: ta). split.
    { eapply star_step; eassumption. }
    split; [ constructor; [ exact I | exact Hsila ] | ].
    subst next. exact Hinb.
  Qed.

  Lemma fgraph_deliver (s1 : fgstate) t1 s2 t2 f orig loc p dst :
    forwarding_reaches ->
    forwarding_tree ->
    no_extra_outputs ->
    forwarding_R s1 t1 s2 t2 ->
    In (loc, (f, orig)) (dest_msgs s1) ->
    graph.path_to (forwarding_graph (dfact_rel f, orig)) loc p dst ->
    exists s1' t1',
      star fgraph_step s1 t1' s1' /\
      Forall silent_event t1' /\
      In (dst, (f, orig)) (dest_msgs s1').
  Proof.
    intros Hreaches Htree Hno. revert s1 t1 loc.
    induction p as [| next p' IH]; intros s1 t1 loc HR Hin (Hpath & Hlast).
    - simpl in Hlast. subst dst. exists s1, []. split; [ apply star_refl | ].
      split; [ constructor | exact Hin ].
    - destruct Hpath as [Hedge Hpath'].
      destruct (fgraph_hop s1 t1 s2 t2 f orig loc next Hreaches Htree Hno HR Hin Hedge)
        as (sa & ta & Hstara & Hsila & Hina).
      destruct (IH sa (ta ++ t1) next
                  (forwarding_R_silent_star _ _ _ _ _ _ Hreaches Htree Hno HR Hstara Hsila)
                  Hina (conj Hpath' ltac:(rewrite last_cons in Hlast; exact Hlast)))
        as (sb & tb & Hstarb & Hsilb & Hinb).
      exists sb, (tb ++ ta). split; [ eapply star_app; eassumption | ].
      split; [ apply Forall_app; split; assumption | exact Hinb ].
  Qed.

  Lemma fgraph_deliver_to_node (s1 : fgstate) t1 s2 t2 n f :
    forwarding_reaches ->
    forwarding_tree ->
    no_extra_outputs ->
    forwarding_R s1 t1 s2 t2 ->
    valid_dest (node_destn n) ->
    In f (queue_at_dest s2 (node_destn n)) ->
    exists s1' t1' orig,
      star fgraph_step s1 t1' s1' /\
      Forall silent_event t1' /\
      In (f, orig) (to_consume_at s1' n).
  Proof.
    intros Hreaches Htree Hno HR Hvalid Hin.
    pose proof HR as HR'. cbv [forwarding_R delivered_to] in HR'. fwd.
    specialize (HR'p6 (node_destn n) Hvalid). fwd.
    eapply Permutation_in in Hin; [ | exact HR'p6p0 ].
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    { cbn [arrived] in Hin. apply in_map_iff in Hin.
      destruct Hin as ((f', orig) & Hfst & Hin). simpl in Hfst. subst f'.
      exists s1, [], orig. split; [ apply star_refl | ].
      split; [ constructor | exact Hin ]. }
    eapply travelling_to_in_inv in Hin; [ | exact HR'p6p1 ].
    destruct Hin as (loc & orig & Hdm & (p & Hpath) & Hroute).
    destruct (fgraph_deliver s1 t1 s2 t2 f orig loc p (loc_of_dest (node_destn n))
                Hreaches Htree Hno HR Hdm Hpath) as (sa & ta & Hstara & Hsila & Hina).
    pose proof (forwarding_R_silent_star _ _ _ _ _ _ Hreaches Htree Hno HR Hstara Hsila) as HRa.
    cbn [loc_of_dest] in Hina. apply in_dest_msgs_inv in Hina.
    destruct Hina as [(m & ms & Hloc & Hgetm & Hpend) | (Hloc & _)]; [ | discriminate Hloc ].
    injection Hloc as Hnm. subst m.
    destruct (fgraph_to_pending sa n ms (f, orig) Hgetm Hpend)
      as (sb & tb & ms' & Hstarb & Hsilb & Hgetb & Hpendb).
    destruct (fgraph_route_keeps sb n ms' f orig Hgetb Hpendb Hroute) as (sc & Hstepc & Hinc).
    exists sc, (O_event (run n (forward_label f)) [] :: (tb ++ ta)), orig.
    split; [ eapply star_step; [ eapply star_app; eassumption | exact Hstepc ] | ].
    split; [ | exact Hinc ].
    constructor; [ exact I | apply Forall_app; split; assumption ].
  Qed.

  Lemma fgraph_deliver_to_output (s1 : fgstate) t1 s2 t2 f :
    forwarding_reaches ->
    forwarding_tree ->
    no_extra_outputs ->
    forwarding_R s1 t1 s2 t2 ->
    In f s2.(graph_output_queue) ->
    exists s1' t1' orig,
      star fgraph_step s1 t1' s1' /\
      Forall silent_event t1' /\
      In (f, orig) s1'.(graph_output_queue).
  Proof.
    intros Hreaches Htree Hno HR Hin.
    pose proof HR as HR'. cbv [forwarding_R delivered_to] in HR'. fwd.
    specialize (HR'p6 output_destn I). fwd. cbn [arrived app] in HR'p6p0.
    eapply Permutation_in in Hin; [ | exact HR'p6p0 ].
    eapply travelling_to_in_inv in Hin; [ | exact HR'p6p1 ].
    destruct Hin as (loc & orig & Hdm & (p & Hpath) & _).
    destruct (fgraph_deliver s1 t1 s2 t2 f orig loc p (loc_of_dest output_destn)
                Hreaches Htree Hno HR Hdm Hpath) as (sa & ta & Hstara & Hsila & Hina).
    cbn [loc_of_dest] in Hina. apply in_dest_msgs_inv in Hina.
    destruct Hina as [(m & ms & Hloc & _ & _) | (_ & Hout)]; [ discriminate Hloc | ].
    exists sa, ta, orig. split; [ exact Hstara | split; [ exact Hsila | exact Hout ] ].
  Qed.

  Lemma fgraph_weak_sims_ngraph :
    forwarding_reaches ->
    forwarding_tree ->
    no_extra_outputs ->
    weak_sim fgraph_step ngraph_step forwarding_R.
  Proof.
    intros Hreaches Htree Hno.
    cbv [weak_sim]. intros.
    destruct (silent_event_dec e) as [Hsil | Hsil].
    { exists s2, []. split; [ apply star_refl | ]. split.
      { symmetry. apply silent_event_inputs, Hsil. }
      eapply forwarding_R_silent_step; eassumption. }
    cbv [fgraph_step] in H0. fwd. invert H0p1.
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
      { intros f orig Hin.
        cbn [forward_to graph_output_queue] in Hin.
        apply in_app_or in Hin. destruct Hin as [Hin | Hin]; [|solve[eauto]].
        apply filter_In in Hin. destruct Hin as [Hin Hkeep].
        destruct Hin as [Heq | []]. fwd.
        apply inb_true_iff in Hkeep.
        apply Hno.
        eapply graph.reaches_step_before; [ apply graph.reaches_self | ].
        apply forwarding_graph_spec. fwd. eauto. }
      split.
      { simpl. apply Forall2_map_map_values'_l, Forall2_map_map_values'_r.
        eapply Forall2_map_impl; [eassumption|]. simpl. intros. assumption. }
      split.
      { apply msgs_reachable_forward_to; [ assumption | apply graph.reaches_self | assumption ]. }
      intros dest Hdest. specialize (Hp6 dest Hdest).
      destruct Hp6 as (Q & HQ & Htr). cbv [delivered_to]. eexists. split.
      { rewrite queue_at_dest_forward_to; try assumption.
        2: { eapply forwarding_compatible_same_domain; [eassumption|].
             eapply Forall2_map_same_domain. eassumption. }
        rewrite arrived_forward_to, HQ. apply Permutation_app_swap_app. }
      rewrite dest_msgs_forward_to by assumption.
      apply travelling_to_app; [ | exact Htr ].
      apply travelling_to_forwarded; try assumption.
      intro H'. simpl in H'. destruct dest; discriminate H'.
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
        { assumption. }
        split.
        { apply Forall2_map_map_values'_r. simpl.
          apply Forall2_map_put_both.
          - eapply Forall2_map_impl; [eassumption|]. simpl. auto.
          - simpl. reflexivity. }
        split.
        { unfold msgs_reachable.
          eapply dm_reachable_perm.
          { eapply dest_msgs_put.
            - eassumption.
            - cbv [all_pending_msgs]. simpl. rewrite !app_assoc.
              apply Permutation_app; [|reflexivity]. apply Permutation_app_comm. }
          apply dm_reachable_app; [ apply dm_reachable_deduced | assumption ]. }
        intros dest Hdest. specialize (Hp6 dest Hdest).
        destruct Hp6 as (Q & HQ & Htr). cbv [delivered_to]. eexists. split.
        { rewrite queue_at_dest_forward_to.
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
          erewrite arrived_put_unchanged by (eassumption || reflexivity).
          rewrite HQ. apply Permutation_app_swap_app. }
        rewrite dest_msgs_put.
        2: eassumption.
        2: { cbv [all_pending_msgs]. simpl. rewrite !app_assoc.
             apply Permutation_app; [|reflexivity]. apply Permutation_app_comm. }
        rewrite map_map.
        apply travelling_to_app; [ | exact Htr ].
        apply travelling_to_deduced. assumption.
      + destruct (Hsil I).
      + cbv [forwarding_R] in H. fwd.
        pose proof @Forall2_map_get_l as Hget. especialize Hget; try eassumption. fwd.
        assert (Hin : In f (queue_at_dest s2 (node_destn n))).
        { eapply delivered_to_arrived_incl.
          { apply Hp6. simpl. apply Hp2. congruence. }
          erewrite arrived_get by exact H0. rewrite H5, map_app.
          apply in_or_app. right. left. reflexivity. }
        erewrite queue_at_dest_get in Hin by exact Hgetp0.
        apply in_split in Hin. destruct Hin as (ms1 & ms2 & Hms).
        do 2 eexists. split.
        { apply star_one. eapply gstep_receive; [ exact Hgetp0 | | exact Hms ].
          rewrite <- Hgetp1. exact H7. }
        split; [reflexivity|]. rewrite forward_to_nil.
        cbv [forwarding_R]. simpl.
        split; [assumption|]. split; [assumption|].
        split.
        { eapply forwarding_compatible_same_domain; [eassumption|].
          eapply same_domain_put_r. exact H0. }
        split; [assumption|].
        split.
        { apply Forall2_map_put_both.
          - eapply Forall2_map_impl; [eassumption|]. simpl. auto.
          - reflexivity. }
        split.
        { unfold msgs_reachable. eapply dm_reachable_perm.
          { eapply dest_msgs_put with (new := []); [ exact H0 | reflexivity ]. }
          simpl. assumption. }
        intros dest Hdest. specialize (Hp6 dest Hdest).
        destruct Hp6 as (Qd & HQd & Htrd). cbv [delivered_to]. exists Qd. split.
        2: { rewrite dest_msgs_put with (new := []); [ | exact H0 | reflexivity ].
             simpl. exact Htrd. }
        rewrite queue_at_dest_put, arrived_put. destr (eqb dest (node_destn n)).
        2: exact HQd.
        erewrite queue_at_dest_get in HQd by exact Hgetp0.
        erewrite arrived_get in HQd by exact H0.
        rewrite Hms, H5, map_app in HQd. cbn [map fst] in HQd.
        rewrite <- !Permutation_middle in HQd. cbn [app] in HQd.
        apply Permutation_cons_inv in HQd.
        cbn [gns_queue gns_node_state fnode_to_consume]. rewrite map_app. exact HQd.
    - destruct e; simpl in H0p0; congruence || fwd. destruct (Hsil I).
    - destruct e; simpl in H0p0; congruence || fwd.
      pose proof forwarding_R_output_incl_rev as Houts. especialize Houts; eauto.
      cbv [incl] in Houts. especialize Houts.
      { apply in_map. rewrite H0. apply in_app_iff. simpl. eauto. }
      apply in_split in Houts. destruct Houts as (oq1 & oq2 & Hoq).
      do 2 eexists. split.
      { apply star_one. apply gstep_output. eassumption. }
      split; [reflexivity|]. simpl.
      cbv [forwarding_R] in *. fwd. simpl.
      split; [assumption|]. split.
      { f_equal. assumption. }
      split; [assumption|]. split.
      { eapply wf_queues_incl; [ | exact Hp3 ]. cbn [graph_output_queue]. rewrite H0.
        apply incl_app; [ apply incl_appl, incl_refl | apply incl_appr, incl_tl, incl_refl ]. }
      split; [assumption|].
      split.
      { unfold msgs_reachable.
        eapply dm_reachable_incl; [ | eassumption ].
        cbv [dest_msgs]. cbn [graph_nodes graph_output_queue]. rewrite H0, !map_app.
        cbn [map]. rewrite !app_assoc. apply incl_middle. }
      intros dest Hdest. specialize (Hp6 dest Hdest).
      destruct Hp6 as (Q & HQ & Htr). cbv [delivered_to].
      erewrite dest_msgs_output_append with (s2 := Build_graph_state _ _) (oms := [m]) in Htr.
      2: { simpl. reflexivity. }
      2: { simpl. rewrite H0. symmetry. apply Permutation_middle. }
      destruct dest.
      2: { exists (oq1 ++ oq2). split; [ reflexivity | ].
           cbn [queue_at_dest arrived app] in HQ. rewrite Hoq in HQ.
           rewrite <- Permutation_middle in HQ. rewrite <- HQ in Htr.
           destruct m. simpl in Htr. apply travelling_to_cons_inv in Htr.
           2: { apply Hp3. rewrite H0. apply in_app_iff. simpl. auto. }
           exact Htr. }
      exists Q. split; [ exact HQ | ].
      destruct m. simpl in Htr. apply travelling_to_cons_inv_unreached in Htr.
      { exact Htr. }
      simpl. intros Hr. apply output_loc_reaches_only in Hr. discriminate Hr.
  Qed.
End __.
