From Stdlib Require Import List Lia.
From coqutil Require Import Datatypes.List.
From Datalog Require Import Datalog Node Graph Smallstep List Map Default Eqb Tactics.
From coqutil Require Import Map.Interface Map.Properties Tactics Tactics.fwd Eqb Decidable.
Import ListNotations.
Import node.

Section Distributed.
  Context `{params : datalog_params}.
  Context {prog_map : map.map node_id program} {prog_map_ok : map.ok prog_map}.

  #[local] Instance sender_label : sender_labelT := source.

  #[local] Instance program_default : WithDefault program :=
    {| program.rules := []; program.meta_rules := [] |}.

  Ltac map_func := cbv [sender_label] in *; Datalog.Util.Tactics.map_func.

  Context (R_senders : rel -> list source).
  Context (R_senders_NoDup : forall R, NoDup (R_senders R)).

  Notation claim := (node.claim R_senders).
  Notation consistent := (node.consistent R_senders).

  Context (rel_forward : source -> destn -> rel -> bool).

  Definition forward (s : source) (d : destn) (f : message) := rel_forward s d (message.rel f).

  Lemma forward_equiv s d a b :
    message.equiv a b ->
    forward s d a = forward s d b.
  Proof.
    intros Heq. unfold forward. f_equal.
    destruct a, b; simpl in Heq; fwd; congruence || reflexivity.
  Qed.

  Context (graph_prog : prog_map).
  Context (Hmrv : Forall_map (fun _ p => program.meta_rules_valid p) graph_prog).
  Context (Hsender : Forall_map (fun n p => node.sends_concl_rels R_senders (node_source n) p) graph_prog).

  Definition prog_at (n : node_id) : program := get_or_default graph_prog n.

  Lemma prog_at_get n p : map.get graph_prog n = Some p -> prog_at n = p.
  Proof. apply get_or_default_Some. Qed.

  Local Notation nstep := (fun n => node.step R_senders (prog_at n) (node_source n)).
  Local Notation nallowed := (node.allowed_inputs R_senders).

  Hint Immediate message.equiv_Equivalence : core.

  Hint Resolve node.expects_num_facts_incl Existsn_ge_submultiset Existsn_le_submultiset submultiset_incl incl_def : core.

  Definition claim_output (pat : fact_pattern) (n : source) (fs : list message) : Prop :=
    In n (R_senders pat.(fact_pattern.rel)) ->
    exists cnt, In (message.done_with pat n cnt) fs.

  Definition consistent_output (pat : fact_pattern) (n : source) (fs : list message) : Prop :=
    In n (R_senders pat.(fact_pattern.rel)) ->
    exists cnt, In (message.done_with pat n cnt) fs /\
      Existsn_ge (message.matches pat) cnt fs.

  Definition allowed_output (n : source) (fs : list message) : Prop :=
    (forall pat src cnt,
       In (message.done_with pat src cnt) fs ->
       n = src /\ Existsn_le (message.matches pat) cnt fs) /\
    (forall f, In f fs -> In n (R_senders (message.rel f))).

  Lemma claim_output_mono pat n ms1 ms2 :
    claim_output pat n ms1 -> incl_mod message.equiv ms1 ms2 -> claim_output pat n ms2.
  Proof.
    cbv [claim_output]. intros H1 Hincl Hn.
    destruct (H1 Hn) as (cnt & Hin).
    destruct (Hincl _ Hin) as (b & Hin2 & Heq).
    destruct b as [nf | pat' src' cnt']; cbn [message.equiv] in Heq; [ congruence | ].
    destruct Heq as (<- & <-). exists cnt'. exact Hin2.
  Qed.

  Lemma consistent_output_mono pat n ms1 ms2 :
    consistent_output pat n ms1 -> submultiset ms1 ms2 -> consistent_output pat n ms2.
  Proof.
    cbv [consistent_output]. intros H1 H2. fwd.
    intros. especialize H1; eauto. fwd. eauto 6.
  Qed.

  Lemma allowed_output_submultiset n : multiset_monotone_dec (allowed_output n).
  Proof.
    cbv [multiset_monotone_dec allowed_output]. intros ? ? H1 H2. fwd.
    split; eauto. intros. especialize H1p0; eauto. fwd. eauto.
  Qed.

  Context {node_map : map.map source (list message)} {node_map_ok : map.ok node_map}.
  Context {count_map : map.map source nat} {count_map_ok : map.ok count_map}.

  Lemma meta_locate pat (partition : node_map) n cnt :
    Forall_map allowed_output partition ->
    In (message.done_with pat n cnt) (concat (values partition)) ->
    exists ms, map.get partition n = Some ms /\ In (message.done_with pat n cnt) ms.
  Proof.
    intros HF Hin. apply In_concat_values in Hin. destruct Hin as (k & ms & Hget & Hin_ms).
    pose proof (HF k ms Hget) as (Hall & _).
    destruct (Hall _ _ _ Hin_ms) as (Hsrc & _). subst k.
    exists ms. split; [ exact Hget | exact Hin_ms ].
  Qed.

  Lemma no_R_matches_off_senders pat (partition : node_map) n ms :
    Forall_map allowed_output partition ->
    map.get partition n = Some ms -> ~ In n (R_senders pat.(fact_pattern.rel)) ->
    Forall (fun f => ~ message.matches pat f) ms.
  Proof.
    intros HF Hget Hnin. apply Forall_forall. intros f Hf Hmatch. apply Hnin.
    pose proof (HF n ms Hget) as (_ & Hsend).
    destruct f as [nf | pat' src' cnt']; [| destruct Hmatch].
    destruct Hmatch as (Hrel & _). rewrite Hrel. exact (Hsend _ Hf).
  Qed.

  Lemma sender_block pat (partition : node_map) n cnt :
    Forall_map allowed_output partition ->
    In (message.done_with pat n cnt) (concat (values partition)) ->
    exists ms, map.get partition n = Some ms /\ In (message.done_with pat n cnt) ms /\
               Existsn_le (message.matches pat) cnt ms.
  Proof.
    intros HF Hin. destruct (meta_locate _ _ _ _ HF Hin) as (ms & Hget & Hin_ms).
    pose proof (HF n ms Hget) as (Hall & _).
    destruct (Hall _ _ _ Hin_ms) as (_ & Hle).
    exists ms. split; [ exact Hget | split; [ exact Hin_ms | exact Hle ] ].
  Qed.

  (* the claim's per-sender expected counts, as a real map (absent senders count 0) *)
  Definition claim_counts (pat : fact_pattern) (ems : list nat) : count_map :=
    map.of_list (combine (R_senders pat.(fact_pattern.rel)) ems).

  Definition count_at (pat : fact_pattern) (ems : list nat) (k : source) : nat :=
    get_or_default (claim_counts pat ems) k.

  Lemma count_at_Some pat ems k c :
    map.get (claim_counts pat ems) k = Some c -> count_at pat ems k = c.
  Proof. apply get_or_default_Some. Qed.

  Lemma count_at_None pat ems k :
    map.get (claim_counts pat ems) k = None -> count_at pat ems k = 0.
  Proof. apply get_or_default_None. Qed.

  Lemma map_count_at pat ems :
    length (R_senders pat.(fact_pattern.rel)) = length ems ->
    map (count_at pat ems) (R_senders pat.(fact_pattern.rel)) = ems.
  Proof.
    intros Hlen. unfold count_at, claim_counts, get_or_default, get_or.
    apply map_get_of_list_zip; [ apply R_senders_NoDup | exact Hlen ].
  Qed.

  Lemma count_at_off pat ems k :
    ~ In k (R_senders pat.(fact_pattern.rel)) -> count_at pat ems k = 0.
  Proof.
    intros Hnin. apply count_at_None, get_of_list_not_In.
    intros Hin. apply in_map_iff in Hin. destruct Hin as ((k' & c) & Heq & Hin).
    cbn in Heq. subst k'. apply Hnin. eapply in_combine_l; exact Hin.
  Qed.

  Lemma count_at_combine pat ems k c :
    length (R_senders pat.(fact_pattern.rel)) = length ems ->
    In (k, c) (combine (R_senders pat.(fact_pattern.rel)) ems) ->
    count_at pat ems k = c.
  Proof.
    intros Hlen Hcomb. apply count_at_Some, map.get_of_list_In_NoDup; [| exact Hcomb].
    rewrite map_fst_combine by exact Hlen. apply R_senders_NoDup.
  Qed.

  Lemma count_at_In pat ems k :
    length (R_senders pat.(fact_pattern.rel)) = length ems ->
    In k (R_senders pat.(fact_pattern.rel)) ->
    map.get (claim_counts pat ems) k = Some (count_at pat ems k).
  Proof.
    intros Hlen Hin.
    rewrite <- (map_fst_combine (R_senders pat.(fact_pattern.rel)) ems Hlen) in Hin.
    apply in_map_iff in Hin. destruct Hin as ((k' & c) & Heq & Hcomb). cbn in Heq. subst k'.
    rewrite (count_at_combine _ _ _ _ Hlen Hcomb).
    apply map.get_of_list_In_NoDup; [| exact Hcomb].
    rewrite map_fst_combine by exact Hlen. apply R_senders_NoDup.
  Qed.

  Lemma counts_get_Forall2 (P : source -> nat -> Prop) pat ems k c :
    Forall2 P (R_senders pat.(fact_pattern.rel)) ems ->
    map.get (claim_counts pat ems) k = Some c ->
    P k c.
  Proof.
    intros HF Hget.
    exact (proj1 (Forall_forall _ _) (Forall2_combine _ _ _ HF) _ (get_of_list_In _ _ _ Hget)).
  Qed.

  Lemma sum_count_at pat ems (partition : node_map) :
    length (R_senders pat.(fact_pattern.rel)) = length ems ->
    incl (R_senders pat.(fact_pattern.rel)) (map.keys partition) ->
    list_sum (List.map (count_at pat ems) (map.keys partition)) = list_sum ems.
  Proof.
    intros Hlen Hsub.
    rewrite (list_sum_map_over_subset (count_at pat ems) (R_senders pat.(fact_pattern.rel))
               (map.keys partition));
      [ f_equal; apply map_count_at; exact Hlen | apply R_senders_NoDup | apply map.keys_NoDup
      | exact Hsub | intros k Hnin; apply count_at_off; exact Hnin ].
  Qed.

  Lemma senders_in_keys pat ems (partition : node_map) :
    Forall_map allowed_output partition ->
    Forall2 (fun k e => In (message.done_with pat k e) (concat (values partition)))
            (R_senders pat.(fact_pattern.rel)) ems ->
    incl (R_senders pat.(fact_pattern.rel)) (map.keys partition).
  Proof.
    intros HF Hems k Hk.
    destruct (Forall2_In_l _ _ _ _ Hems Hk) as (em & _ & Hmeta).
    destruct (meta_locate _ _ _ _ HF Hmeta) as (ms & Hget & _).
    eapply map.in_keys; exact Hget.
  Qed.

  (*each node's sent multiset stays within the count the claim assigns it*)
  Lemma counts_bound pat ems (partition : node_map) k ms :
    Forall_map allowed_output partition ->
    Forall2 (fun k e => In (message.done_with pat k e) (concat (values partition)))
            (R_senders pat.(fact_pattern.rel)) ems ->
    map.get partition k = Some ms ->
    Existsn_le (message.matches pat) (count_at pat ems k) ms.
  Proof.
    intros HF Hems Hget.
    destruct (map.get (claim_counts pat ems) k) as [c|] eqn:Ec.
    - rewrite (count_at_Some _ _ _ _ Ec).
      pose proof (counts_get_Forall2 _ _ _ _ _ Hems Ec) as Hmeta.
      destruct (sender_block _ _ _ _ HF Hmeta) as (ms' & Hget' & _ & Hle).
      map_func. assumption.
    - rewrite (count_at_None _ _ _ Ec). apply Existsn_le_0_Forall_not.
      eapply no_R_matches_off_senders; [ exact HF | exact Hget | ].
      intros Hin.
      rewrite count_at_In in Ec by (eauto using Forall2_length). discriminate.
  Qed.

  Lemma allowed_of_outputs (partition : node_map) :
    Forall_map allowed_output partition -> nallowed (concat (values partition)).
  Proof.
    intros HF pat ems Hems.
    assert (Hlen : length (R_senders pat.(fact_pattern.rel)) = length ems)
      by (eapply Forall2_length; exact Hems).
    rewrite <- (sum_count_at pat ems partition Hlen (senders_in_keys _ _ _ HF Hems)).
    apply Existsn_le_concat_map. intros k ms Hget.
    exact (counts_bound _ _ _ _ _ HF Hems Hget).
  Qed.

  Lemma consistent_good_holds :
    consistent_good claim claim_output consistent_output allowed_output consistent.
  Proof.
    intros pat partition Hallow Hclaim. cbv [node.claim] in Hclaim.
    split.
    - intros n ms Hget. cbv [claim_output]. intros Hn.
      destruct (Hclaim n Hn) as (cnt & Hin).
      destruct (meta_locate _ _ _ _ Hallow Hin) as (ms' & Hget' & Hin_ms).
      map_func. exists cnt. assumption.
    - split.
      + intros Hcons. cbv [node.consistent node.expects_num_facts] in Hcons.
        destruct Hcons as (num & (ems & Hexpect & Hnum) & Hge). subst num.
        assert (Hlen : length (R_senders pat.(fact_pattern.rel)) = length ems)
          by (eapply Forall2_length; exact Hexpect).
        rewrite <- (sum_count_at pat ems partition Hlen
                      (senders_in_keys _ _ _ Hallow Hexpect)) in Hge.
        pose proof (Existsn_squeeze_map (message.matches pat) (count_at pat ems) partition Hge
                      (fun k ms Hget => counts_bound _ _ _ _ _ Hallow Hexpect Hget)) as Hsq.
        intros n ms Hget. cbv [consistent_output]. intros Hn.
        destruct (Forall2_In_l _ _ _ _ Hexpect Hn) as (em & Hcomb & Hmeta).
        exists em. split.
        * destruct (meta_locate _ _ _ _ Hallow Hmeta) as (ms' & Hget' & Hin_ms).
          map_func. exact Hin_ms.
        * rewrite <- (count_at_combine _ _ _ _ Hlen Hcomb). exact (Hsq n ms Hget).
      + intros HcoF. cbv [node.consistent node.expects_num_facts].
        assert (Hbuild : Forall (fun k => exists cnt ms, map.get partition k = Some ms /\
                    In (message.done_with pat k cnt) ms /\ Existsn_ge (message.matches pat) cnt ms)
                    (R_senders pat.(fact_pattern.rel))).
        { apply Forall_forall. intros k Hk. destruct (Hclaim k Hk) as (cnt0 & Hin0).
          destruct (meta_locate _ _ _ _ Hallow Hin0) as (ms & Hget & _).
          specialize (HcoF k ms Hget). cbv [consistent_output] in HcoF.
          destruct (HcoF Hk) as (cnt & Hin & Hge).
          exists cnt, ms. split; [ exact Hget | split; [ exact Hin | exact Hge ] ]. }
        apply Forall_exists_r_Forall2 in Hbuild. destruct Hbuild as (ems & Hbuild2).
        exists (list_sum ems). split.
        * exists ems. split; [ | reflexivity ].
          eapply Forall2_impl; [ exact Hbuild2 | ]. intros k cnt (ms & Hget & Hin & _).
          apply In_concat_values. exists k, ms. split; [ exact Hget | exact Hin ].
        * assert (Hsub : incl (R_senders pat.(fact_pattern.rel)) (map.keys partition)).
          { intros k Hk. destruct (Forall2_In_l _ _ _ _ Hbuild2 Hk) as (cnt & _ & (ms & Hget & _)).
            eapply map.in_keys; exact Hget. }
          rewrite <- (sum_count_at pat ems partition
                        ltac:(eauto using Forall2_length) Hsub).
          apply Existsn_ge_concat_map. intros k ms Hget.
          destruct (map.get (claim_counts pat ems) k) as [c|] eqn:Ec.
          -- rewrite (count_at_Some _ _ _ _ Ec).
             pose proof (counts_get_Forall2 _ _ _ _ _ Hbuild2 Ec)
               as (ms' & Hget' & _ & Hge_ms).
             map_func. exact Hge_ms.
          -- rewrite (count_at_None _ _ _ Ec). apply Eg_zero.
  Qed.

  Context {gmap : map.map node_id (@graph_node_state message action_label state)}.
  Context {gmap_ok : map.ok gmap}.
  Context {msg_map : map.map node_id (list message)} {msg_map_ok : map.ok msg_map}.

  Definition graph_node_init : @graph_node_state message action_label state :=
    {| gns_node_state := node.init; gns_trace := []; gns_queue := [] |}.

  Definition initial_graph_nodes : gmap :=
    map_values' (fun _ _ => graph_node_init) graph_prog.

  Definition initial_graph_state :=
    {| graph_nodes := initial_graph_nodes; graph_output_queue := @nil message |}.

  Lemma initial_graph_state_get n gns :
    map.get initial_graph_state.(graph_nodes) n = Some gns ->
    exists np, map.get graph_prog n = Some np /\ gns = graph_node_init.
  Proof.
    intros H. unfold initial_graph_state, initial_graph_nodes in H. cbn [graph_nodes] in H.
    rewrite get_map_values' in H.
    destruct (map.get graph_prog n) as [np|] eqn:Hg; cbn [option_map] in H; [ | discriminate ].
    exists np. split; [ reflexivity | congruence ].
  Qed.

  Lemma initial_graph_state_empty n gns :
    map.get initial_graph_state.(graph_nodes) n = Some gns ->
    gns.(gns_trace) = [] /\ gns.(gns_queue) = [].
  Proof.
    intros H. apply initial_graph_state_get in H. destruct H as (np & _ & ->).
    split; reflexivity.
  Qed.

  Lemma nallowed_multiset_monotone : multiset_monotone_dec nallowed.
  Proof. intros l1 l2 Hl2 Hsub. eapply node.allowed_inputs_submultiset; eauto. Qed.

  Lemma nstep_input_total n : input_total (nstep n).
  Proof. intros s m. eexists. apply node.input_step. Qed.

  Lemma forward_rel_level s d f g :
    message.rel f = message.rel g -> forward s d f = forward s d g.
  Proof. intros Heq. unfold forward. rewrite Heq. reflexivity. Qed.

  Lemma node_outputs_well_formed (k : node_id) (p : program)
      (forward : source -> destn -> message -> bool)
      (forward_rel : forall s d f g,
          message.rel f = message.rel g -> forward s d f = forward s d g) :
    node.sends_concl_rels R_senders (node_source k) p ->
    outputs_well_formed (node.step R_senders p (node_source k))
      (good_node_output forward claim_output consistent_output allowed_output k) node.init.
  Proof.
    intros Hconcl_send t s Hstar dest. set (name := node_source k) in *.
    assert (Hsend : forall s0 f, node.can_deduce R_senders p name s0 f ->
                      In name (R_senders (message.rel f))).
    { intros s0 f Hnf. apply node.can_deduce_concl_rel in Hnf. exact (Hconcl_send _ Hnf). }
    assert (Hso : s.(state.sent) = flat_map outputs_of t)
      by (eapply node.sent_eq_outputs; exact Hstar).
    assert (Hsrc : forall pat src num,
               In (message.done_with pat src num) s.(state.sent) -> src = name)
      by (eapply node.sent_source_correct; exact Hstar).
    assert (Hcnt : forall pat num,
               In (message.done_with pat name num) s.(state.sent) ->
               Existsn (message.matches pat) num s.(state.sent))
      by (eapply node.sent_counts_correct; exact Hstar).
    rewrite <- Hso. split.
    - cbv [allowed_output]. split.
      + intros pat src cnt Hin.
        apply filter_In in Hin. destruct Hin as (Hin_sent & Hfwd).
        pose proof (Hsrc pat src cnt Hin_sent) as Hsk. subst src.
        split; [ reflexivity | ].
        apply Existsn_le_filter.
        eapply Existsn_le_of_Existsn; [ exact (Hcnt pat cnt Hin_sent) | lia ].
      + intros f Hin. apply filter_In in Hin. destruct Hin as (Hin_sent & _).
        eapply node.sent_rel_sender; [ exact Hsend | exact Hstar | exact Hin_sent ].
    - intros pat Hclaim. cbv [claim_output consistent_output] in Hclaim |- *.
      intros Hn. destruct (Hclaim Hn) as (cnt & Hin_meta).
      exists cnt. split; [ exact Hin_meta | ].
      apply filter_In in Hin_meta. destruct Hin_meta as (Hin_sent & Hfwd).
      apply Existsn_ge_filter.
      + intros x Hmx. destruct x as [nf | pat' src' cnt']; [| destruct Hmx].
        destruct Hmx as (Hrel & _).
        rewrite (forward_rel name (node_destn dest) (message.normal nf)
                   (message.done_with pat name cnt)); [ exact Hfwd | ].
        cbn [message.rel]. congruence.
      + eapply Existsn_ge_of_Existsn; [ exact (Hcnt pat cnt Hin_sent) | lia ].
  Qed.

  Lemma nodes_good_holds :
    Forall_map (node_good forward message.equiv claim claim_output consistent_output allowed_output
                  consistent nallowed nstep) initial_graph_state.(graph_nodes).
  Proof.
    intros k v Hkv. apply initial_graph_state_get in Hkv. fwd.
    pose proof node.might_implies_will' as H.
    especialize H; eauto. apply miw'_iff_miw_and_monotone' in H; auto. fwd.
    cbv [node_good graph_node_init gns_node_state].
    erewrite prog_at_get by eassumption.
    ssplit; try eassumption.
    apply node_outputs_well_formed; [ exact forward_rel_level | eapply Hsender; eauto ].
  Qed.

  Definition distributed_step := graph_step forward nstep.

  Theorem distributed_might_implies_will :
    might_implies_will_equiv distributed_step message.equiv
      (graph_inputs_allowed forward allowed_output) initial_graph_state.
  Proof.
    intros.
    pose proof initial_graph_state_empty as Hemp.
    assert (Hoq : initial_graph_state.(graph_output_queue) = []) by reflexivity.
    eapply graph_might_implies_will; try eassumption.
    - exact message.equiv_Equivalence.
    - exact forward_equiv.
    - exact (node.claim_mono R_senders).
    - exact claim_output_mono.
    - exact (node.consistent_mono R_senders).
    - exact consistent_output_mono.
    - exact consistent_good_holds.
    - exact nallowed_multiset_monotone.
    - exact allowed_output_submultiset.
    - exact allowed_of_outputs.
    - exact nstep_input_total.
    - exact nodes_good_holds.
  Qed.

End Distributed.
