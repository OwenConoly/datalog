From Stdlib Require Import List Permutation RelationClasses Classical_Prop Lia.
From coqutil Require Import Datatypes.List.
From Datalog Require Import Datalog Node Graph Smallstep List Map Eqb Tactics.
From coqutil Require Import Map.Interface Map.Properties Tactics Tactics.fwd Eqb Decidable.
Import ListNotations.

Section Distributed.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.

  Context (R_senders : rel -> list node_name).
  Context (R_senders_NoDup : forall R, NoDup (R_senders R)).

  Context (rel_input_allowed : node_id -> rel -> bool).
  Context (rel_forward : node_id -> node_id -> rel -> bool).
  Context (rel_visible : node_id -> rel -> bool).

  Definition input_allowed n (f : dfact) := rel_input_allowed n (dfact_rel f).
  Definition forward n1 n2 (f : dfact) := rel_forward n1 n2 (dfact_rel f).
  Definition output_visible n (f : dfact) := rel_visible n (dfact_rel f).

  Lemma output_visible_equiv n a b :
    dfact_equiv a b ->
    output_visible n a = output_visible n b.
  Proof.
    intros Heq. unfold output_visible. f_equal.
    destruct a, b; simpl in Heq; fwd; congruence || reflexivity.
  Qed.

  Lemma forward_equiv n1 n2 a b :
    dfact_equiv a b ->
    forward n1 n2 a = forward n1 n2 b.
  Proof.
    intros Heq. unfold forward. f_equal.
    destruct a, b; simpl in Heq; fwd; congruence || reflexivity.
  Qed.

  (* The graph runs one node program [np] replicated across nodes. *)
  Context (np : node_prog).
  Context (Hmrv : meta_rules_valid np.(np_rules)).

  Local Notation nstep := (node_step R_senders np).
  Local Notation nallowed := (allowed_inputs R_senders).

  #[local] Instance nequiv_equiv : Equivalence dfact_equiv.
  Proof.
    constructor.
    - intros f. apply dfact_equiv_refl.
    - intros f1 f2. apply dfact_equiv_sym.
    - intros [R1 a1 | R1 m1 s1 c1] [R2 a2 | R2 m2 s2 c2] [R3 a3 | R3 m3 s3 c3] H12 H23;
        cbn [dfact_equiv] in *; try congruence.
      destruct H12 as (-> & -> & ->), H23 as (-> & -> & ->). repeat split.
  Qed.

  Definition stmt : Type := (rel * list (option T))%type.

  Definition claim (s : stmt) (l : list dfact) :=
    let '(R, mf_args) := s in
    forall src, In src (R_senders R) ->
      exists cnt, In (meta_dfact R mf_args src cnt) l.

  Lemma claim_mono s ms1 ms2 :
    claim s ms1 -> incl_mod dfact_equiv ms1 ms2 -> claim s ms2.
  Proof.
    cbv [claim]. intros H Hincl. fwd.
    intros. especialize H; eauto. fwd.
    cbv [incl_mod] in Hincl. especialize Hincl; eauto. fwd.
    cbv [dfact_equiv] in Hinclp1. fwd. eauto.
  Qed.

  Definition claim_output (s : stmt) (n : node_name) (fs : list dfact) : Prop :=
    let '(R, mf_args) := s in
    In n (R_senders R) -> exists cnt, In (meta_dfact R mf_args n cnt) fs.

  Definition consistent_output (s : stmt) (n : node_name) (fs : list dfact) : Prop :=
    let '(R, mf_args) := s in
    In n (R_senders R) ->
    exists cnt, In (meta_dfact R mf_args n cnt) fs /\
      Existsn_ge (dfact_matches R mf_args) cnt fs.

  Definition allowed_output (n : node_name) (fs : list dfact) : Prop :=
    (forall R mf_args src cnt,
       In (meta_dfact R mf_args src cnt) fs ->
       n = src /\ Existsn_le (dfact_matches R mf_args) cnt fs) /\
    (forall f, In f fs -> In n (R_senders (dfact_rel f))).

  Definition consistent (s : stmt) (l : list dfact) : Prop :=
    let '(R, mf_args) := s in
    exists num, expect_num_R_facts R_senders R mf_args l num /\
             Existsn_ge (dfact_matches R mf_args) num l.

  Lemma unstupid_Forall2_impl {A B} (R1 R2 : A -> B -> _) x y :
    Forall2 R1 x y ->
    (forall x y, R1 x y -> R2 x y) ->
    Forall2 R2 x y.
  Proof. intros. eapply Forall2_impl; eauto. Qed.

  Lemma expect_num_R_facts_incl R mf_args l1 l2 num :
    expect_num_R_facts R_senders R mf_args l1 num -> incl l1 l2 ->
    expect_num_R_facts R_senders R mf_args l2 num.
  Proof.
    cbv [expect_num_R_facts]. intros. fwd.
    Fail solve [eauto using Forall2_impl].
    eauto using unstupid_Forall2_impl.
  Qed.

  Lemma incl_def {A} x (xs ys : list A) :
    incl xs ys ->
    In x xs ->
    In x ys.
  Proof. auto. Qed.

  Hint Resolve expect_num_R_facts_incl Existsn_ge_submultiset Existsn_le_submultiset submultiset_incl incl_def : core.
  Lemma consistent_mono s ms1 ms2 :
    consistent s ms1 -> submultiset ms1 ms2 -> consistent s ms2.
  Proof. cbv [consistent]. intros. fwd. eauto 6. Qed.

  Lemma consistent_output_mono s n ms1 ms2 :
    consistent_output s n ms1 -> submultiset ms1 ms2 -> consistent_output s n ms2.
  Proof.
    cbv [consistent_output]. intros H1 H2. fwd.
    intros. especialize H1; eauto. fwd. eauto 6.
  Qed.

  Lemma allowed_output_submultiset n : multiset_monotone_dec (allowed_output n).
  Proof.
    cbv [multiset_monotone_dec allowed_output]. intros ? ? H1 H2. fwd.
    split; eauto. intros. especialize H1p0; eauto. fwd. eauto.
  Qed.

  Lemma Forall2_In_combine {A B} (R : A -> B -> Prop) xs ys x y :
    Forall2 R xs ys -> In (x, y) (combine xs ys) -> R x y.
  Proof.
    induction 1 as [| a b xs' ys' Hab HF IH]; simpl; [ contradiction | ].
    intros [Heq | Hin]; [ injection Heq as -> ->; exact Hab | exact (IH Hin) ].
  Qed.

  #[local] Instance node_name_eqdec : EqDecider (@eqb node_name _).
  Proof. intros x y. apply Eqb_ok_BoolSpec. Qed.

  Context {node_map : map.map (option node_id) (list dfact)} {node_map_ok : map.ok node_map}.
  Context {count_map : map.map node_name nat} {count_map_ok : map.ok count_map}.

  Lemma meta_locate R mf_args (partition : node_map) n cnt :
    Forall_map allowed_output partition ->
    In (meta_dfact R mf_args n cnt) (concat (values partition)) ->
    exists ms, map.get partition n = Some ms /\ In (meta_dfact R mf_args n cnt) ms.
  Proof.
    intros HF Hin. apply In_concat_values in Hin. destruct Hin as (k & ms & Hget & Hin_ms).
    pose proof (HF k ms Hget) as (Hall & _).
    destruct (Hall _ _ _ _ Hin_ms) as (Hsrc & _). subst k.
    exists ms. split; [ exact Hget | exact Hin_ms ].
  Qed.

  Lemma no_R_matches_off_senders R mf_args (partition : node_map) n ms :
    Forall_map allowed_output partition ->
    map.get partition n = Some ms -> ~ In n (R_senders R) ->
    Forall (fun f => ~ dfact_matches R mf_args f) ms.
  Proof.
    intros HF Hget Hnin. apply Forall_forall. intros f Hf Hmatch. apply Hnin.
    pose proof (HF n ms Hget) as (_ & Hsend).
    destruct Hmatch as (nf_args & -> & _). exact (Hsend _ Hf).
  Qed.

  Lemma sender_block R mf_args (partition : node_map) n cnt :
    Forall_map allowed_output partition ->
    In (meta_dfact R mf_args n cnt) (concat (values partition)) ->
    exists ms, map.get partition n = Some ms /\ In (meta_dfact R mf_args n cnt) ms /\
               Existsn_le (dfact_matches R mf_args) cnt ms.
  Proof.
    intros HF Hin. destruct (meta_locate _ _ _ _ _ HF Hin) as (ms & Hget & Hin_ms).
    pose proof (HF n ms Hget) as (Hall & _).
    destruct (Hall _ _ _ _ Hin_ms) as (_ & Hle).
    exists ms. split; [ exact Hget | split; [ exact Hin_ms | exact Hle ] ].
  Qed.

  (* the claim's per-sender expected counts, as a real map *)
  Definition count_at R (ems : list nat) (k : node_name) : nat :=
    match map.get (map.of_list (combine (R_senders R) ems) : count_map) k with
    | Some c => c | None => 0 end.

  Lemma map_count_at R ems :
    length (R_senders R) = length ems -> map (count_at R ems) (R_senders R) = ems.
  Proof.
    intros Hlen. unfold count_at. apply map_get_of_list_zip; [ apply R_senders_NoDup | exact Hlen ].
  Qed.

  Lemma count_at_off R ems k : ~ In k (R_senders R) -> count_at R ems k = 0.
  Proof.
    intros Hnin. unfold count_at. rewrite get_of_list_not_In; [ reflexivity | ].
    intros Hin. apply in_map_iff in Hin. destruct Hin as ((k' & c) & Heq & Hin).
    cbn in Heq. subst k'. apply Hnin. eapply in_combine_l; exact Hin.
  Qed.

  Lemma count_at_In R ems k :
    length (R_senders R) = length ems -> In k (R_senders R) ->
    map.get (map.of_list (combine (R_senders R) ems) : count_map) k = Some (count_at R ems k).
  Proof.
    intros Hlen Hin.
    assert (Hnd : NoDup (List.map fst (combine (R_senders R) ems)))
      by (rewrite map_fst_combine by exact Hlen; apply R_senders_NoDup).
    rewrite <- (map_fst_combine (R_senders R) ems Hlen) in Hin.
    apply in_map_iff in Hin. destruct Hin as ((k' & c) & Heq & Hcomb). cbn in Heq. subst k'.
    rewrite (map.get_of_list_In_NoDup (combine (R_senders R) ems) Hnd k c Hcomb).
    unfold count_at. rewrite (map.get_of_list_In_NoDup (combine (R_senders R) ems) Hnd k c Hcomb).
    reflexivity.
  Qed.

  Lemma sum_count_at R ems (partition : node_map) :
    length (R_senders R) = length ems ->
    incl (R_senders R) (map.keys partition) ->
    list_sum (List.map (count_at R ems) (map.keys partition)) = list_sum ems.
  Proof.
    intros Hlen Hsub.
    rewrite (list_sum_map_over_subset (count_at R ems) (R_senders R) (map.keys partition));
      [ f_equal; apply map_count_at; exact Hlen | apply R_senders_NoDup | apply map.keys_NoDup
      | exact Hsub | intros k Hnin; apply count_at_off; exact Hnin ].
  Qed.

  Lemma allowed_of_outputs (partition : node_map) :
    Forall_map allowed_output partition -> nallowed (concat (values partition)).
  Proof.
    intros HF R mf_args ems Hems.
    assert (Hlen : length (R_senders R) = length ems) by (eapply Forall2_length; exact Hems).
    assert (Hsub : incl (R_senders R) (map.keys partition)).
    { intros k Hk. destruct (Forall2_In_l _ _ _ _ Hems Hk) as (em & _ & Hmeta).
      destruct (meta_locate _ _ _ _ _ HF Hmeta) as (ms & Hget & _). eapply map.in_keys; exact Hget. }
    rewrite <- (sum_count_at R ems partition Hlen Hsub).
    apply Existsn_le_concat_map. intros k ms Hget.
    destruct (map.get (map.of_list (combine (R_senders R) ems) : count_map) k) as [c|] eqn:Ec.
    - assert (count_at R ems k = c) by (unfold count_at; rewrite Ec; reflexivity).
      rewrite H. pose proof (Forall2_In_combine _ _ _ _ _ Hems (get_of_list_In _ _ _ Ec)) as Hmeta.
      destruct (sender_block _ _ _ _ _ HF Hmeta) as (ms' & Hget' & _ & Hle).
      pose proof (eq_trans (eq_sym Hget') Hget) as Heq. injection Heq as ->. exact Hle.
    - assert (count_at R ems k = 0) by (unfold count_at; rewrite Ec; reflexivity).
      rewrite H. apply Existsn_le_0_Forall_not.
      eapply no_R_matches_off_senders; [ exact HF | exact Hget | ].
      intros Hin. rewrite (count_at_In R ems k Hlen Hin) in Ec. discriminate.
  Qed.

  Lemma consistent_good_holds :
    consistent_good claim claim_output consistent_output allowed_output consistent.
  Proof.
    intros [R mf_args] partition Hallow Hclaim. cbn [claim] in Hclaim.
    split.
    - intros n ms Hget. cbn [claim_output]. intros Hn.
      destruct (Hclaim n Hn) as (cnt & Hin).
      destruct (meta_locate _ _ _ _ _ Hallow Hin) as (ms' & Hget' & Hin_ms).
      pose proof (eq_trans (eq_sym Hget') Hget) as Heq; injection Heq as ->. exists cnt. exact Hin_ms.
    - split.
      + intros Hcons. cbn [consistent] in Hcons.
        destruct Hcons as (num & (ems & Hexpect & Hnum) & Hge). subst num.
        assert (Hlen : length (R_senders R) = length ems) by (eapply Forall2_length; exact Hexpect).
        assert (Hsub : incl (R_senders R) (map.keys partition)).
        { intros k Hk. destruct (Forall2_In_l _ _ _ _ Hexpect Hk) as (em & _ & Hmeta).
          destruct (meta_locate _ _ _ _ _ Hallow Hmeta) as (ms & Hget & _). eapply map.in_keys; exact Hget. }
        assert (Hle : Forall_map (fun k ms => Existsn_le (dfact_matches R mf_args) (count_at R ems k) ms)
                                 partition).
        { intros k ms Hget.
          destruct (map.get (map.of_list (combine (R_senders R) ems) : count_map) k) as [c|] eqn:Ec.
          - assert (Hc : count_at R ems k = c) by (unfold count_at; rewrite Ec; reflexivity). rewrite Hc.
            pose proof (Forall2_In_combine _ _ _ _ _ Hexpect (get_of_list_In _ _ _ Ec)) as Hmeta.
            destruct (sender_block _ _ _ _ _ Hallow Hmeta) as (ms' & Hget' & _ & Hle_ms).
            pose proof (eq_trans (eq_sym Hget') Hget) as Heq; injection Heq as ->. exact Hle_ms.
          - assert (Hc : count_at R ems k = 0) by (unfold count_at; rewrite Ec; reflexivity). rewrite Hc.
            apply Existsn_le_0_Forall_not.
            eapply no_R_matches_off_senders; [ exact Hallow | exact Hget | ].
            intros Hin. rewrite (count_at_In R ems k Hlen Hin) in Ec. discriminate. }
        rewrite <- (sum_count_at R ems partition Hlen Hsub) in Hge.
        pose proof (Existsn_squeeze_map (dfact_matches R mf_args) (count_at R ems) partition Hge Hle) as Hsq.
        intros n ms Hget. cbn [consistent_output]. intros Hn.
        destruct (Forall2_In_l _ _ _ _ Hexpect Hn) as (em & Hcomb & Hmeta).
        exists em. split.
        * destruct (meta_locate _ _ _ _ _ Hallow Hmeta) as (ms' & Hget' & Hin_ms).
          pose proof (eq_trans (eq_sym Hget') Hget) as Heq; injection Heq as ->. exact Hin_ms.
        * assert (Hen : count_at R ems n = em).
          { unfold count_at.
            rewrite (map.get_of_list_In_NoDup (combine (R_senders R) ems)
                       ltac:(rewrite map_fst_combine by exact Hlen; apply R_senders_NoDup) n em Hcomb).
            reflexivity. }
          rewrite <- Hen. exact (Hsq n ms Hget).
      + intros HcoF. cbn [consistent].
        assert (Hbuild : Forall (fun k => exists cnt ms, map.get partition k = Some ms /\
                    In (meta_dfact R mf_args k cnt) ms /\ Existsn_ge (dfact_matches R mf_args) cnt ms)
                    (R_senders R)).
        { apply Forall_forall. intros k Hk. destruct (Hclaim k Hk) as (cnt0 & Hin0).
          destruct (meta_locate _ _ _ _ _ Hallow Hin0) as (ms & Hget & _).
          specialize (HcoF k ms Hget). cbn [consistent_output] in HcoF.
          destruct (HcoF Hk) as (cnt & Hin & Hge).
          exists cnt, ms. split; [ exact Hget | split; [ exact Hin | exact Hge ] ]. }
        apply Forall_exists_r_Forall2 in Hbuild. destruct Hbuild as (ems & Hbuild2).
        exists (list_sum ems). split.
        * exists ems. split; [ | reflexivity ].
          eapply Forall2_impl; [ | exact Hbuild2 ]. intros k cnt (ms & Hget & Hin & _).
          apply In_concat_values. exists k, ms. split; [ exact Hget | exact Hin ].
        * assert (Hlen : length (R_senders R) = length ems) by (eapply Forall2_length; exact Hbuild2).
          assert (Hsub : incl (R_senders R) (map.keys partition)).
          { intros k Hk. destruct (Forall2_In_l _ _ _ _ Hbuild2 Hk) as (cnt & _ & (ms & Hget & _)).
            eapply map.in_keys; exact Hget. }
          rewrite <- (sum_count_at R ems partition Hlen Hsub).
          apply Existsn_ge_concat_map. intros k ms Hget.
          destruct (map.get (map.of_list (combine (R_senders R) ems) : count_map) k) as [c|] eqn:Ec.
          -- assert (Hc : count_at R ems k = c) by (unfold count_at; rewrite Ec; reflexivity). rewrite Hc.
             pose proof (Forall2_In_combine _ _ _ _ _ Hbuild2 (get_of_list_In _ _ _ Ec))
               as (ms' & Hget' & _ & Hge_ms).
             pose proof (eq_trans (eq_sym Hget') Hget) as Heq; injection Heq as ->. exact Hge_ms.
          -- assert (Hc : count_at R ems k = 0) by (unfold count_at; rewrite Ec; reflexivity). rewrite Hc.
             apply Eg_zero.
  Qed.

  Context {graph_state : map.map node_id (@graph_node_state dfact dfact_mod_count node_state)}.
  Context {graph_state_ok : map.ok graph_state}.
  Context {msg_map : map.map node_id (list dfact)} {msg_map_ok : map.ok msg_map}.
  Context {omap : map.map node_id (list (dfact * node_id))} {omap_ok : map.ok omap}.
  Context (initial_gs : graph_state).
  Context (initial_gs_empty :
             forall n gns, map.get initial_gs n = Some gns ->
                           gns.(gns_trace) = [] /\ gns.(gns_queue) = []).
  Context (initial_gs_node_init :
             forall n gns, map.get initial_gs n = Some gns ->
                           gns.(gns_node_state) = node_init).

  Lemma nallowed_multiset_monotone : multiset_monotone_dec nallowed.
  Proof. intros l1 l2 Hl2 Hsub. eapply allowed_inputs_submultiset; eauto. Qed.

  Lemma nstep_input_total : input_total nstep.
  Proof. intros s m. eexists. apply node_input_step. Qed.

  Lemma nodes_good_holds :
    Forall_map (node_good forward dfact_equiv claim claim_output consistent_output allowed_output
                          consistent nallowed nstep) initial_gs.
  Admitted.

  Local Notation gstep := (graph_step input_allowed forward output_visible nstep).
  Local Notation gia := (graph_inputs_allowed allowed_output).

  Theorem distributed_might_implies_will
          (t : list (IO_event (@graph_label dfact dfact_mod_count) (dfact * node_id)))
          (gs : graph_state) (o : dfact * node_id) :
    star gstep initial_gs t gs ->
    gia (inputs_of t) ->
    might_output gstep gs t o ->
    will_output_equiv gstep (graph_equiv dfact_equiv) gia gs t o.
  Proof.
    intros.
    eapply graph_might_implies_will; try eassumption.
    - exact nequiv_equiv.
    - exact output_visible_equiv.
    - exact forward_equiv.
    - exact claim_mono.
    - exact consistent_mono.
    - exact consistent_output_mono.
    - exact consistent_good_holds.
    - exact nallowed_multiset_monotone.
    - exact allowed_output_submultiset.
    - exact allowed_of_outputs.
    - exact nstep_input_total.
    - exact nodes_good_holds.
  Qed.

End Distributed.
