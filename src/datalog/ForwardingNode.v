From Stdlib Require Import List Permutation Morphisms.
From Datalog Require Import List Datalog Smallstep Tactics Graph Map Default Node.
From GraphSearch Require Import GraphInterface Examples.
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
  Context {V : Type} {eqbV : Eqb V} {gi : graph.graph V} {gok : graph.ok gi}.

  (* A connected subgraph of a tree is a tree: local-tree-ness propagates from the
     root to any reachable vertex. *)
  Lemma is_locally_tree_reaches (g : gi) root v :
    graph.reaches g root v ->
    graph.is_locally_tree g root ->
    graph.is_locally_tree g v.
  Proof.
  Admitted.

  Context {X : Type}.

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
    - apply graph_incoming_Proper. symmetry. exact Hperm.
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

  Lemma travelling_to_forwarding_step_exchange s f orig dm dm' dest qmsg qcopies queue :
    forwarding_step s f orig dm dm' ->
    travelling_to [(loc_of_source s, (f, orig))] dest qmsg ->
    travelling_to (map (fun d' => (loc_of_dest d', (f, orig)))
                     (fforward s (dfact_rel f, orig))) dest qcopies ->
    travelling_to dm dest (qmsg ++ queue) ->
    travelling_to dm' dest (qcopies ++ queue).
  Proof.
    intros (rest & Hdm & Hdm') Hmsg Hcopies Htr.
    rewrite Hdm in Htr. rewrite Hdm'.
    apply travelling_to_app.
    - exact Hcopies.
    - eapply travelling_to_app_inv; [ | exact Hmsg ]. exact Htr.
  Qed.

  Lemma travelling_to_cons_inv dm dest f orig queue :
    In dest (nforward orig (dfact_rel f)) ->
    travelling_to ((loc_of_dest dest, (f, orig)) :: dm) dest (f :: queue) ->
    travelling_to dm dest queue.
  Proof.
    intros Hnf (queue' & Hqeq & HF & HP).
    assert (Hrefl : graph.reachesb (forwarding_graph (dfact_rel f, orig))
                      (loc_of_dest dest) (loc_of_dest dest) = true).
    { destr (graph.reachesb (forwarding_graph (dfact_rel f, orig))
               (loc_of_dest dest) (loc_of_dest dest));
        [ reflexivity | exfalso; eauto using graph.reaches_self ]. }
    assert (Hheadgi : forall l,
               graph_incoming (forwarding_graph (dfact_rel f, orig)) (loc_of_dest dest)
                 (msgs_to_pebbles (dfact_rel f) orig ((loc_of_dest dest, (f, orig)) :: l))
               = f :: graph_incoming (forwarding_graph (dfact_rel f, orig)) (loc_of_dest dest)
                       (msgs_to_pebbles (dfact_rel f) orig l)).
    { intro l. change ((loc_of_dest dest, (f, orig)) :: l) with ([(loc_of_dest dest, (f, orig))] ++ l).
      rewrite msgs_to_pebbles_app, graph_incoming_app.
      cbv [msgs_to_pebbles graph_incoming]. cbn [filter map msg_matches].
      rewrite !eqb_refl_true by typeclasses eauto. cbn [andb filter map].
      rewrite Hrefl. cbn [map]. reflexivity. }
    assert (Hheadother : forall R o l, (R = dfact_rel f -> o <> orig) ->
               msgs_to_pebbles R o ((loc_of_dest dest, (f, orig)) :: l) = msgs_to_pebbles R o l).
    { intros R o l Hne. change ((loc_of_dest dest, (f, orig)) :: l) with ([(loc_of_dest dest, (f, orig))] ++ l).
      rewrite msgs_to_pebbles_app. cbv [msgs_to_pebbles]. cbn [filter map msg_matches].
      destr (eqb R (dfact_rel f) && eqb o orig)%bool; cbn [map app]; try reflexivity.
      exfalso. destruct E as [-> ->]. apply Hne; reflexivity. }
    assert (Hfilterother : forall R o (l : list (dfact * source)), (R = dfact_rel f -> o <> orig) ->
               filter (msg_matches R o) ((f, orig) :: l) = filter (msg_matches R o) l).
    { intros R o l Hne. cbn [filter msg_matches].
      destr (eqb R (dfact_rel f) && eqb o orig)%bool; try reflexivity.
      exfalso. destruct E as [-> ->]. apply Hne; reflexivity. }
    assert (Hbin : In (f, orig) queue').
    { pose proof (HP (dfact_rel f) orig Hnf) as HPb. rewrite Hheadgi in HPb.
      assert (Hb : In f (map fst (filter (msg_matches (dfact_rel f) orig) queue'))).
      { eapply Permutation_in; [ exact HPb | left; reflexivity ]. }
      apply in_map_iff in Hb. destruct Hb as ((f', o') & Hfst & Hinf). cbn in Hfst. subst f'.
      apply filter_In in Hinf. destruct Hinf as [Hinf Hm]. cbn [msg_matches] in Hm.
      rewrite eqb_refl_true in Hm by typeclasses eauto.
      destr (eqb orig o'); [ | discriminate Hm ]. exact Hinf. }
    apply in_split in Hbin. destruct Hbin as (l1 & l2 & Hsplit).
    assert (Htx : travelling_to dm dest (map fst (l1 ++ l2))).
    { exists (l1 ++ l2). split; [reflexivity | split].
      - subst queue'. apply Forall_app in HF. destruct HF as [HF1 HF2].
        inversion HF2. apply Forall_app. split; assumption.
      - intros R o Hprem. specialize (HP R o Hprem). subst queue'.
        destr (eqb R (dfact_rel f) && eqb o orig)%bool.
        + destruct E as [-> ->].
          rewrite Hheadgi in HP. rewrite filter_app in HP. cbn [filter msg_matches] in HP.
          rewrite !eqb_refl_true in HP by typeclasses eauto. cbn [andb map] in HP.
          rewrite map_app in HP. cbn [map fst] in HP.
          rewrite filter_app, map_app.
          apply (Permutation_cons_inv (a := f)).
          etransitivity; [ exact HP | ]. symmetry. apply Permutation_middle.
        + assert (Hne : R = dfact_rel f -> o <> orig).
          { intros HR Ho. destruct E; congruence. }
          rewrite (Hheadother R o) in HP by exact Hne.
          rewrite filter_app in HP. rewrite (Hfilterother R o) in HP by exact Hne.
          rewrite <- filter_app in HP. exact HP. }
    assert (Hpy : Permutation (map fst (l1 ++ l2)) queue).
    { assert (Heq : map fst l1 ++ f :: map fst l2 = f :: queue).
      { subst queue'. rewrite map_app in Hqeq. cbn [map] in Hqeq. symmetry. exact Hqeq. }
      rewrite map_app. apply (Permutation_cons_inv (a := f)). rewrite <- Heq.
      apply Permutation_middle. }
    rewrite Hpy in Htx. exact Htx.
  Qed.

  Lemma travelling_to_cons_inv_unreached loc f orig dm dest queue :
    ~ graph.reaches (forwarding_graph (dfact_rel f, orig)) loc (loc_of_dest dest) ->
    travelling_to ((loc, (f, orig)) :: dm) dest queue ->
    travelling_to dm dest queue.
  Proof.
    intros Hnr (queue' & Hqeq & HF & HP).
    exists queue'. split; [exact Hqeq | split; [exact HF | ]].
    intros R o Hprem. specialize (HP R o Hprem).
    assert (Hhead : graph_incoming (forwarding_graph (R, o)) (loc_of_dest dest)
                      (msgs_to_pebbles R o [(loc, (f, orig))]) = []).
    { cbv [msgs_to_pebbles graph_incoming]. cbn [filter map msg_matches].
      destr (eqb R (dfact_rel f) && eqb o orig)%bool; cbn [map filter]; try reflexivity.
      destruct E as [-> ->].
      destr (graph.reachesb (forwarding_graph (dfact_rel f, orig)) loc (loc_of_dest dest));
        cbn [map]; [ exfalso; apply Hnr; assumption | reflexivity ]. }
    change ((loc, (f, orig)) :: dm) with ([(loc, (f, orig))] ++ dm) in HP.
    rewrite msgs_to_pebbles_app, graph_incoming_app, Hhead in HP.
    cbn [app] in HP. exact HP.
  Qed.

  Lemma travelling_to_single src d dest :
    forwarding_reaches ->
    travelling_to [(loc_of_source src, (d, src))] dest
      (if nforwardb src dest d then [d] else []).
  Proof.
    intros Hreaches. destruct (nforwardb src dest d) eqn:Hnf.
    - exists [(d, src)]. split; [reflexivity | split].
      + constructor; [ | constructor ].
        cbv [nforwardb] in Hnf. apply inb_true_iff. exact Hnf.
      + intros R orig Hprem.
        cbv [msgs_to_pebbles graph_incoming]. cbn [filter map msg_matches].
        destr (eqb R (dfact_rel d) && eqb orig src)%bool; cbn [map filter]; try reflexivity.
        destruct E as [-> ->].
        assert (Hre : graph.reaches (forwarding_graph (dfact_rel d, src))
                        (loc_of_source src) (loc_of_dest dest)) by (apply Hreaches; exact Hprem).
        destr (graph.reachesb (forwarding_graph (dfact_rel d, src))
                 (loc_of_source src) (loc_of_dest dest));
          [ cbn [map]; reflexivity | contradiction ].
    - exists []. split; [reflexivity | split; [constructor | ]].
      intros R orig Hprem.
      cbv [msgs_to_pebbles graph_incoming]. cbn [filter map msg_matches].
      destr (eqb R (dfact_rel d) && eqb orig src)%bool; cbn [map filter]; try reflexivity.
      exfalso. destruct E as [-> ->]. cbv [nforwardb] in Hnf.
      rewrite <- inb_true_iff in Hprem. congruence.
  Qed.

  Lemma travelling_to_deduced n dest outs :
    forwarding_reaches ->
    travelling_to (map (fun x => (node_loc n, (x, node_source n))) outs) dest
      (filter (nforwardb (node_source n) dest) outs).
  Proof.
    intros Hreaches. induction outs as [| x outs' IH].
    - exists []. split; [reflexivity | split; [constructor | ]].
      intros R orig Hprem. reflexivity.
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
      (forall dest, valid_dest dest -> travelling_to (dest_msgs s1) dest (queue_at_dest s2 dest)).

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
    intros HR. cbv [forwarding_R] in HR. fwd.
    specialize (HRp6 output_destn I). cbn [queue_at_dest] in HRp6.
    intros f Hf. apply in_map_iff in Hf. destruct Hf as ((f', orig) & Heq & Hin).
    simpl in Heq. subst f'.
    apply (travelling_to_in _ output_destn _ f orig HRp6).
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
    forwarding_compatible s.(graph_nodes) ->
    map.get s.(graph_nodes) n = Some ns ->
    Permutation (all_pending_msgs ns) ((f, orig) :: all_pending_msgs v') ->
    forwarding_step (node_source n) f orig
      (dest_msgs s)
      (dest_msgs (forward_to (fforwardb (node_source n)) [(f, orig)]
                    {| graph_nodes := map.put s.(graph_nodes) n v';
                       graph_output_queue := s.(graph_output_queue) |})).
  Proof.
    intros Hcompat Hget Hperm. cbv [forwarding_step]. cbn [loc_of_source].
    eexists. split.
    - etransitivity; [ apply (dest_msgs_get_remove s n ns Hget) | ].
      rewrite (Permutation_map (fun m => (node_loc n, m)) Hperm).
      cbn [map]. rewrite <- app_comm_cons. reflexivity.
    - rewrite dest_msgs_forward_to.
      2: { eapply forwarding_compatible_same_domain; [ exact Hcompat | ].
           cbn [graph_nodes]. eapply same_domain_put_r. exact Hget. }
      apply Permutation_app_head.
      etransitivity.
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
    - eapply dest_msgs_dequeue; eassumption.
    - exact Htr.
  Qed.

  Lemma fgraph_weak_sims_ngraph :
    forwarding_reaches ->
    forwarding_tree ->
    no_extra_outputs ->
    weak_sim fgraph_step ngraph_step forwarding_R.
  Proof.
    intros Hreaches Htree Hno.
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
      intros.
      rewrite dest_msgs_forward_to by assumption.
      rewrite queue_at_dest_forward_to; try assumption.
      2: { eapply forwarding_compatible_same_domain; [eassumption|].
           eapply Forall2_map_same_domain. eassumption. }
      apply travelling_to_app; [|solve[auto]].
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
        apply travelling_to_deduced. assumption.
      + simpl. simpl in H7. cbv [forwarding_R] in H. fwd.
        Tactics.destruct_one_match_hyp.
        -- pose proof @Forall2_map_get_l as Hget. especialize Hget; try eassumption.
           fwd. rewrite Hgetp1 in *.
           eapply travelling_to_in in E.
           2: { apply Hp6. simpl. apply Hp2. congruence. }
           2: { eapply in_node_dest_msgs; [ exact H0 | ].
                cbv [all_pending_msgs]. apply in_or_app. right. rewrite H5.
                apply in_or_app. right. left. reflexivity. }
           simpl in E. rewrite Hgetp0 in E. simpl in E. apply in_split in E. fwd.
           do 2 eexists. split.
           { apply star_one. apply gstep_receive; eassumption. }
           split; [reflexivity|].
           cbv [forwarding_R]. simpl.
           split; [assumption|]. split; [assumption|]. split.
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
             - eapply msgs_reachable_pending; [ exact Hp5 | exact H0 | exact H5 ].
             - apply forwarding_graph_spec. exists (node_source n), output_destn.
               split; [ exact Hkeep | split; reflexivity ]. }
           split.
           { apply Forall2_map_map_values'_l. simpl.
             apply Forall2_map_put_both.
             - eapply Forall2_map_impl; [exact Hp4|]. simpl. auto.
             - simpl. reflexivity. }
           split.
           { apply msgs_reachable_forward_to.
             - eapply forwarding_compatible_same_domain; [exact Hp2|].
               cbn [graph_nodes]. eapply same_domain_put_r. exact H0.
             - eapply msgs_reachable_pending; [ exact Hp5 | exact H0 | exact H5 ].
             - eapply msgs_reachable_put_incl.
               + exact H0.
               + eapply incl_all_pending_dequeue; [ reflexivity | reflexivity | exact H5 ].
               + exact Hp5. }
           intros dest Hdest. specialize (Hp6 dest Hdest).
           rewrite queue_at_dest_put. destr (eqb dest (node_destn n)).
           ++ eapply travelling_to_forwarding_step_exchange with (qmsg := [f]) (qcopies := []).
              { eapply dest_msgs_dequeue; [ exact Hp2 | exact H0 | ].
                eapply all_pending_msgs_dequeue; [ reflexivity | reflexivity | exact H5 ]. }
              { admit. }
              { admit. }
              simpl in Hp6. rewrite Hgetp0 in Hp6. simpl in Hp6. rewrite E in Hp6.
              rewrite <- Permutation_middle in Hp6. exact Hp6.
           ++ eapply travelling_to_dequeue; try eassumption.
              eapply all_pending_msgs_dequeue; [ reflexivity | reflexivity | exact H5 ].
        -- subst. do 2 eexists. split; [apply star_refl|]. split; [reflexivity|].
           cbv [forwarding_R]. simpl. split; [assumption|]. split; [assumption|].
           split.
           { eapply forwarding_compatible_same_domain; [eassumption|].
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
             - eapply msgs_reachable_pending; [ exact Hp5 | exact H0 | exact H5 ].
             - apply forwarding_graph_spec. exists (node_source n), output_destn.
               split; [ exact Hkeep | split; reflexivity ]. }
           pose proof @Forall2_map_get_l as Hget. especialize Hget; try eassumption.
           fwd.
           split.
           { apply Forall2_map_map_values'_l. simpl.
             eapply Forall2_map_put_l; [|eassumption|].
             2: { simpl. assumption. }
             eapply Forall2_map_impl; [eassumption|]. simpl. auto. }
           split.
           { apply msgs_reachable_forward_to.
             - eapply forwarding_compatible_same_domain; [exact Hp2|].
               cbn [graph_nodes]. eapply same_domain_put_r. exact H0.
             - eapply msgs_reachable_pending; [ exact Hp5 | exact H0 | exact H5 ].
             - eapply msgs_reachable_put_incl.
               + exact H0.
               + eapply incl_all_pending_dequeue; [ reflexivity | reflexivity | exact H5 ].
               + exact Hp5. }
           intros dest Hdest. specialize (Hp6 dest Hdest).
           destr (eqb dest (node_destn n)).
           ++ eapply travelling_to_forwarding_step_exchange with (qmsg := []) (qcopies := []).
              { eapply dest_msgs_dequeue; [ exact Hp2 | exact H0 | ].
                eapply all_pending_msgs_dequeue; [ reflexivity | reflexivity | exact H5 ]. }
              { admit. }
              { admit. (*note: this is the same as the previous admit.*) }
              exact Hp6.
           ++ eapply travelling_to_dequeue; try eassumption.
              eapply all_pending_msgs_dequeue; [ reflexivity | reflexivity | exact H5 ].
    - destruct e; simpl in H0p0; congruence || fwd. invert H1.
      do 2 eexists. split.
      { apply star_refl. }
      split; [reflexivity|].
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
      intros. rewrite dest_msgs_put with (new := []).
      2: eassumption.
      2: { cbv [all_pending_msgs]. simpl. rewrite H2. rewrite <- !app_assoc.
           apply Permutation_app_head. symmetry. apply Permutation_middle. }
      simpl. auto.
    - destruct e; simpl in H0p0; congruence || fwd.
      pose proof forwarding_R_output_incl_rev as Houts. especialize Houts; eauto.
      cbv [incl] in Houts. especialize Houts.
      { apply in_map. rewrite H0. apply in_app_iff. simpl. eauto. }
      apply in_split in Houts. fwd.
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
      intros dest Hdest. apply Hp6 in Hdest.
      erewrite dest_msgs_output_append with (s2 := Build_graph_state _ _) (oms := [m]) in Hdest.
      2: { simpl. reflexivity. }
      2: { simpl. rewrite H0. symmetry. apply Permutation_middle. }
      destruct dest.
      2: { simpl. cbn [queue_at_dest] in Hdest. rewrite Houts in Hdest.
           simpl in Hdest. rewrite <- Permutation_middle in Hdest.
           destruct m. simpl in Hdest. apply travelling_to_cons_inv in Hdest.
           2: { apply Hp3. rewrite H0. apply in_app_iff. simpl. auto. }
           assumption. }
      simpl. simpl in Hdest. destruct m.
      apply travelling_to_cons_inv_unreached in Hdest.
      { apply Hdest. }
      simpl. intros Hr. apply output_loc_reaches_only in Hr. discriminate Hr.
  Admitted.
End __.
