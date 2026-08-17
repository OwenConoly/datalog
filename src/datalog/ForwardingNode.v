From Stdlib Require Import List Lia Permutation Classical_Prop RelationClasses Morphisms.
From Datalog Require Import List Datalog Smallstep Tactics Graph Map Default Eqb Node.
From GraphSearch Require Import GraphInterface Examples.
From coqutil Require Import Map.Interface Map.Properties.
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

Section pebbles.
  Context {V X : Type} {eqbV : Eqb V} {gi : graph.graph V} {gok : graph.ok gi}.

  Definition pebble_step (g : gi) (v : V) (x : X) (ps1 ps2 : list (V * X)) : Prop :=
    exists rest,
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

  Lemma graph_incoming_pebble_step (g : gi) v x target ps1 ps2 :
    graph.is_locally_tree g v ->
    v <> target ->
    pebble_step g v x ps1 ps2 ->
    Permutation (graph_incoming g target ps1) (graph_incoming g target ps2).
  Proof.
  Admitted.
End pebbles.

Variant source :=
  | node_source (_ : node_id)
  | input_source.

Variant destn :=
  | node_destn (_ : node_id)
  | output_destn.

Variant location :=
  | node_loc (_ : node_id)
  | input_loc
  | output_loc.

Section __.
  Context {rel : relT} {T : valueT}.
  Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.
  Context {node_prog node_state : Type}.
  Context {label : Type}.
  Context (node_step : node_prog -> node_state -> IO_event label dfact -> node_state -> Prop).
  (* Context (finput_locs : rel -> list destn). *)
  (* Context (finput_locs_NoDup : forall R, NoDup (finput_locs R)). *)
  (* Context (ninput_locs : rel -> list node_id). *)
  (* Context (noutput_locs : rel -> list node_id). *)
  (* Context (foutput_locs : rel -> source -> list source). *)
  Context (nforward : source -> rel -> list destn).
  Context {forwarding_table : map.map (rel * source) (list destn)}.
  Context {forwarding_tables : map.map source forwarding_table}.
  Context {forwarding_table_ok : map.ok forwarding_table}.
  Context {forwarding_tables_ok : map.ok forwarding_tables}.
  Context {graph : graph.graph (option node_id)} {graph_ok : graph.ok graph}.
  Context {oops : map.map nat (list dfact)} {oops_ok : map.ok oops}.
  Context (fts : forwarding_tables).
  Context (prog_at : node_id -> node_prog).

  Local Notation fgraph_node_state :=
    (graph_node_state (dfact * option node_id) (fnode_label dfact label) (fnode_state node_state dfact)).
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
  Local Notation pebble := (source * dfact)%type.

  Check List.inb.
  Definition ngraph_step :=
    graph_step
      (fun src dst m => existsb (eqb dst) (nforward src (dfact_rel m)))
      (fun dst m => existsb (eqb dst) (ninput_locs (dfact_rel m)))
      (
      (fun n => node_step (prog_at n)).



  Definition recipients (orig : option node_id) R : list node_id :=
    match orig with
    | Some n => nforward n R
    | None => ninput_locs R
    end.

  Definition recipients_of (m : dfact * option node_id) :=
    let '(f, o) := m in recipients o (dfact_rel f).

  Definition foutput_visible n (m : dfact * option node_id) :=
    let '(f, ) := m in output_visible n f.

  Definition finput_at dst (m : dfact * option node_id) :=
    let '(f, _) := m in existsb (eqb dst) (finput_locs (dfact_rel f)).

  Definition fforward (src : node_id) (mn : rel * option node_id) : list node_id :=
    get_or_default (get_or_default fts src) mn.

  Definition corresp (e : IO_event) (e' : fIO_event) : Prop :=
    match e with
    | O_event lbl msgs => exists msgs', e' = O_event lbl msgs' /\ msgs = map fst msgs'
    | I_event msg => e' = I_event (msg, None)
    end.

  Definition fprog_at n : fnode_prog node_prog dfact :=
    {| fnode_rules := prog_at n;
       fnode_keep := fun f orig => existsb (eqb n) (recipients_of (f, orig)) |}.

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

  Definition forwarding_tree :=
    forall R orig,
      graph.is_locally_tree (forwarding_graph (R, orig)) orig.

  Definition forwarding_reaches :=
    forall R orig n',
      In n' (recipients orig R) ->
      graph.reaches (forwarding_graph (R, orig)) orig (Some n').

  Lemma forwarding_graph_spec mn v w :
    graph.edge (forwarding_graph mn) v w <->
    match v with
    | None => In w (map Some (finput_locs (fst mn)))
    | Some src => In w (map Some (fforward src mn))
    end.
  Proof.
    cbv [forwarding_graph fforward]. rewrite graph.edge_put_edges.
    assert (Hemp : forall (m : forwarding_tables) k', map.get m k' = None ->
                   In w (map Some (get_or_default (get_or_default m k') mn)) <-> False).
    { intros m k' Hk. cbv [get_or_default get_or]. rewrite Hk.
      cbv [default map_default list_default]. rewrite map.get_empty. cbn [map In]. tauto. }
    assert (Hfold : forall v0,
      graph.edge (map.fold (fun g src tbl => graph.put_edges g (Some src) (map Some (get_or_default tbl mn))) graph.empty fts) v0 w
      <-> match v0 with None => False | Some src => In w (map Some (get_or_default (get_or_default fts src) mn)) end).
    { apply (map.fold_spec (fun processed acc => forall v0,
        graph.edge acc v0 w <-> match v0 with None => False | Some src => In w (map Some (get_or_default (get_or_default processed src) mn)) end)).
      - intros [src|]; rewrite graph.edge_empty_iff; [ | reflexivity ].
        rewrite (Hemp map.empty src (map.get_empty _)). reflexivity.
      - intros k tbl processed acc Hget IH v0.
        rewrite graph.edge_put_edges, (IH v0). destruct v0 as [src|].
        2: { split; [ intros [[] | [Hc _]]; congruence | intros [] ]. }
        rewrite get_or_default_put. destr (eqb k src).
        + rewrite (Hemp processed src Hget). graph.
        + graph. }
    rewrite (Hfold v). destruct v; graph.
  Qed.

  Lemma edge_forwarding_graph_None mn v :
    graph.edge (forwarding_graph mn) None v <-> In v (map Some (finput_locs (fst mn))).
  Proof. exact (forwarding_graph_spec mn None v). Qed.

  Lemma edges_forwarding_graph_None mn :
    Permutation (graph.edges (forwarding_graph mn) None) (map Some (finput_locs (fst mn))).
  Proof.
    apply NoDup_Permutation.
    - apply graph.edges_NoDup.
    - apply FinFun.Injective_map_NoDup.
      + intros x y H. congruence.
      + apply finput_locs_NoDup.
    - intros v. exact (edge_forwarding_graph_None mn v).
  Qed.

  Lemma edge_forwarding_graph_Some_shape mn u v :
    graph.edge (forwarding_graph mn) u v -> exists n, v = Some n.
  Proof. rewrite forwarding_graph_spec. destruct u; intros H; apply in_map_iff in H; fwd; eauto. Qed.

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

  Lemma to_pebbles_map_values'_enqueue R orig (g : node_id -> list (dfact * option node_id)) (s : fgraph_state) :
    Permutation
      (to_pebbles R orig (map_values' (fun n ns => enqueue (g n) ns) s))
      (flat_map (fun '(n, _) => map (fun '(f, _) => (Some n, f)) (filter (msg_matches R orig) (g n)))
                (map.tuples s)
       ++ to_pebbles R orig s).
  Proof.
    cbv [to_pebbles].
    rewrite tuples_map_values', flat_map_map.
    apply flat_map_app_perm. intros [n ns]. cbv beta iota.
    rewrite all_pending_msgs_enqueue, filter_app, map_app. reflexivity.
  Qed.

  Lemma to_pebbles_map_values'_enqueue_nomatch R orig
    (g : node_id -> list (dfact * option node_id)) (s : fgraph_state) :
    (forall n m, In m (g n) -> msg_matches R orig m = false) ->
    Permutation (to_pebbles R orig (map_values' (fun n ns => enqueue (g n) ns) s))
                (to_pebbles R orig s).
  Proof.
    intros Hnm. rewrite to_pebbles_map_values'_enqueue, flat_map_all_nil; [ reflexivity | ].
    intros [n ns] _. cbn [fst snd].
    rewrite filter_ext_in with (g := fun _ => false); [ rewrite filter_false; reflexivity | ].
    intros m Hm. apply (Hnm n m Hm).
  Qed.

  Lemma to_pebbles_get_remove R orig (g : fgraph_state) n ns :
    map.get g n = Some ns ->
    Permutation
      (to_pebbles R orig g)
      (map (fun '(f, _) => (Some n, f)) (filter (msg_matches R orig) (all_pending_msgs ns))
       ++ to_pebbles R orig (map.remove g n)).
  Proof.
    intros Hget. cbv [to_pebbles]. rewrite (tuples_get_perm _ _ _ Hget). reflexivity.
  Qed.

  Definition forwarding_compatible (s : fgraph_state) : Prop :=
    forall mn u n, graph.edge (forwarding_graph mn) u (Some n) -> map.get s n <> None.

  Lemma forwarding_compatible_sub_domain (s s' : fgraph_state) :
    forwarding_compatible s ->
    map.sub_domain s s' ->
    forwarding_compatible s'.
  Proof.
    intros Hcompat Hsub mn u n Hedge Hnone.
    eapply Hcompat in Hedge. apply Hedge.
    destruct (map.get s n) as [v|] eqn:E; [ | reflexivity ].
    apply Hsub in E. fwd. congruence.
  Qed.

  Definition forwarding_R
    (s1 : fgraph_state) (t1 : list IO_event)
    (s2 : ngraph_state) (t2 : list nIO_event) : Prop :=
    flat_map inputs_of t1 = flat_map inputs_of t2 /\
      incl (flat_map outputs_of t1) (flat_map outputs_of t2) /\
      forwarding_compatible s1 /\
      Forall2_map (fun destn fgns ngns =>
                     fgns.(gns_node_state).(fnode_node) = ngns.(gns_node_state))
                  s1 s2 /\
      Forall_map (fun destn queue =>
                       exists queue' : list (dfact * option node_id),
                         queue = map fst queue' /\
                         Forall (fun m => In destn (recipients_of m)) queue' /\
                         forall R orig,
                           In destn (recipients orig R) ->
                           Permutation
                             (graph_incoming (forwarding_graph (R, orig)) (Some destn) (to_pebbles R orig s1))
                             (map fst (filter (msg_matches R orig) queue')))
        (map_values' (fun _ => gns_queue) s2).

  Hint Constructors NoDup : core.
  Lemma pebble_step_forward (s : fgraph_state) orig loc f :
    forwarding_compatible s ->
    pebble_step (forwarding_graph (dfact_rel f, orig)) loc f
      ((loc, f) :: to_pebbles (dfact_rel f) orig s)
      (to_pebbles (dfact_rel f) orig
         (map_values'
            (fun dst ns =>
               enqueue (filter (fun _ => existsb (eqb (Some dst))
                                  (graph.edges (forwarding_graph (dfact_rel f, orig)) loc)) [(f, orig)]) ns)
            s)).
  Proof.
    intros Hcompat. cbv [pebble_step]. eexists. split; [reflexivity|].
    etransitivity; [apply to_pebbles_map_values'_enqueue|].
    apply Permutation_app; [| reflexivity].
    apply NoDup_Permutation.
    { apply List.NoDup_flat_map.
      - apply map.tuples_NoDup.
      - intros [n ns] _. cbn [fst snd filter].
        Tactics.destruct_one_match; try solve [simpl; auto].
        cbn [filter]. Tactics.destruct_one_match; simpl; auto.
      - intros [? ?] [? ?]. intros.
        rewrite in_map_iff in *. fwd.
        rewrite map.tuples_spec in *. congruence. }
    { apply FinFun.Injective_map_NoDup.
      - intros x y H. congruence.
      - apply graph.edges_NoDup. }
    intros x. rewrite in_flat_map, in_map_iff. split; intros; fwd.
    - destruct x0 as [n ns].
      apply in_map_iff in Hp1. fwd.
      apply filter_In in Hp1p1. fwd.
      apply filter_In in Hp1p1p0. fwd. simpl in *.
      destruct Hp1p1p0p0; [|contradiction]. subst.
      eexists. split; [reflexivity|]. apply Exists_exists in Hp1p1p0p1.
      fwd. assumption.
    - pose proof edge_forwarding_graph_Some_shape as E. especialize E; eauto. fwd.
      destruct (map.get s n) as [ns|] eqn:E.
      2: { exfalso. eapply Hcompat; eassumption. }
      exists (n, ns). split.
      + rewrite map.tuples_spec. exact E.
      + cbn [fst snd]. apply in_map_iff. exists (f, orig). split; [reflexivity|].
        apply filter_In. split.
        * apply filter_In. split; [ left; reflexivity | ].
          apply existsb_exists. exists (Some n). split; [ exact Hp1 | ].
          apply eqb_refl_true.
          typeclasses eauto.
        * cbn [msg_matches]. rewrite !eqb_refl_true by typeclasses eauto. reflexivity.
  Qed.

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
      split; [reflexivity|]. cbv [forwarding_R] in *. fwd. split.
      { simpl. f_equal. assumption. }
      split.
      { simpl. assumption. }
      split.
      { eapply forwarding_compatible_sub_domain; [eassumption|].
        apply same_domain_map_values'. }
      split.
      { simpl. apply Forall2_map_map_values'_l, Forall2_map_map_values'_r.
        eapply Forall2_map_impl; [eassumption|]. simpl. intros. assumption. }
      apply Forall_map_map_values' in Hp4.
      apply Forall_map_map_values'. apply Forall_map_map_values'.
      intros k v Hget. specialize (Hp4 k v Hget). simpl in Hp4. fwd.
      eexists ((if existsb (eqb k) (ninput_locs (dfact_rel d)) then [(d, None)] else []) ++ _).
      split.
      { cbn [gns_queue enqueue filter]. rewrite map_app.
        Tactics.destruct_one_match; simpl; try eassumption. f_equal. assumption. }
      split.
      { apply Forall_app. split; [|assumption]. Tactics.destruct_one_match.
        - apply Exists_exists in E. fwd. auto.
        - auto. }
      intros R o HR.
      destruct (msg_matches R o (d, None)) eqn:E.
      2: { rewrite to_pebbles_map_values'_enqueue_nomatch.
           2: { intros n m Hm. apply filter_In in Hm. destruct Hm as [[Hm|[]] _].
                subst. assumption. }
           rewrite filter_app, map_app.
           destruct (existsb (eqb k) (ninput_locs (dfact_rel d))).
           - cbn [filter]. rewrite E. cbn [map app]. auto.
           - cbn [filter map app]. auto. }
      simpl in E. fwd.
      simpl in HR. Tactics.destruct_one_match.
      2: { rewrite Forall_forall in E. apply E in HR.
           rewrite eqb_refl_true in HR by typeclasses eauto. congruence. }
      erewrite map_values'_ext.
      1: rewrite <- graph_incoming_pebble_step.
      4: { apply pebble_step_forward. assumption. }
      2: { apply Htree. }
      3: { intros dst ns. f_equal. cbn [filter]. cbv [finput_at].
           f_equal. eassert (existsb _ _ = _) as ->; [|reflexivity].
           apply Bool.eq_true_iff_eq. do 2 rewrite <- List.existsb_eqb_in.
           pose proof forwarding_graph_spec as E'. cbv [graph.edge] in E'.
           rewrite E'. rewrite in_map_iff. simpl. split; intros; fwd; eauto. }
      2: { congruence. }
      simpl. rewrite! eqb_refl_true by typeclasses eauto. simpl.
      eassert ((_, _) :: _ = [(_, _)] ++ _) as -> by reflexivity.
      eassert (d :: _ = [_] ++ _) as -> by reflexivity.
      rewrite graph_incoming_app. apply Permutation_app; [|auto].
      cbv [graph_incoming]. simpl.
      Tactics.destruct_one_match; fwd.
      { reflexivity. }
      exfalso. apply E0. auto.
    - destruct e; simpl in H0p0; congruence || fwd. invert H1.
      + cbv [forwarding_R] in H. fwd. pose proof H0 as H0'.
        eapply Forall2_map_get_l in H0; [|eassumption].
        simpl in H0. fwd.
        do 2 eexists. split.
        { apply star_one. apply gstep_run; try eassumption. rewrite <- H0p1.
          eassumption. }
        simpl. split; [reflexivity|]. erewrite map_values'_ext.
        1: rewrite map_values'_id.
        2: { intros k v. simpl. destruct v. reflexivity. }
        cbv [enqueue]. cbv [forwarding_R]. split.
        { simpl. assumption. }
        split.
        { simpl. apply incl_appr. assumption. }
        split.
        { eapply forwarding_compatible_sub_domain; [eassumption|].
          apply map.sub_domain_put_r. apply map.sub_domain_refl. }
        split.
        { apply Forall2_map_map_values'_r. simpl.
          apply Forall2_map_put_both.
          - eapply Forall2_map_impl; [eassumption|]. simpl. auto.
          - simpl. reflexivity. }
        rewrite map_values'_map_values'. rewrite map_values'_put. simpl.
        rewrite map.put_noop with (m := map_values' _ _).
        2: { rewrite get_map_values'. rewrite H0p0. simpl. reflexivity. }
        apply Forall_map_map_values'. apply Forall_map_map_values' in Hp4.
        intros k v Hkv. apply Hp4 in Hkv. clear Hp4. fwd.
        eexists (map (fun x => (x, Some n)) _ ++ _). split.
        { rewrite map_app, map_map. simpl. rewrite map_id. f_equal. eassumption. }
        split.
        { apply Forall_app. split; [|assumption]. apply List.Forall_map.
          apply List.Forall_filter. simpl. intros. fwd. apply Exists_exists in H.
          fwd. assumption. }
        intros R o HR.
        rewrite to_pebbles_get_remove.
        2: { apply map.get_put_same. }
        rewrite map.remove_put_same.
        especialize Hkvp2; eauto. rewrite to_pebbles_get_remove in Hkvp2 by eassumption.
        rewrite filter_app with (l' := queue'). rewrite map_app with (l' := filter _ queue').
        rewrite <- Hkvp2. clear Hkvp2.
        rewrite !graph_incoming_app. rewrite app_assoc with (n := graph_incoming _ _ _).
        apply Permutation_app. 2: reflexivity.
        cbv [all_pending_msgs]. simpl.
        rewrite !filter_app, !map_app, !graph_incoming_app.
        repeat rewrite app_assoc.
        apply Permutation_app; [|reflexivity].
        rewrite Permutation_app_comm.
        apply Permutation_app; [|reflexivity].
        cbv [graph_incoming].
        rewrite !filter_map_swap, !map_map. cbn [fst snd]. rewrite !map_id.
        simpl. destr (eqb o (Some n)).
        2: { erewrite filter_ext with (f := fun _ => (_ && _)%bool).
             2: { intros. apply Bool.andb_false_r. }
             erewrite filter_ext with (f := fun _ => (_ && _)%bool).
             2: { intros. apply Bool.andb_false_r. }
             do 2 rewrite filter_false. simpl. reflexivity. }
        destr (graph.reachesb (forwarding_graph (R, Some n)) (Some n) (Some k)).
        2: { exfalso. apply E. apply Hreaches. assumption. }
        rewrite filter_true. rewrite filter_comm.
        erewrite filter_ext_in with (f := fun _ => existsb _ _). 1: rewrite filter_true.
        2: { intros ? H. apply filter_In in H. fwd. destruct Hp5; [|discriminate].
             subst. apply List.existsb_eqb_in. assumption. }
        reflexivity.
      + simpl in H7. simpl. do 2 eexists. split.
        { apply star_refl. }
        split; [reflexivity|].
        simpl. cbv [forwarding_R].
 simpl.  Admitted.
End __.
