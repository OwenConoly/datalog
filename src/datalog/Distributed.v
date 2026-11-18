From Stdlib Require Import List Lia.
From coqutil Require Import OmniSmallstepCombinators.
From Datalog Require Import Datalog Node Graph2WithIO IOGraph Smallstep List Eqb Tactics FinTypeclass.
From coqutil Require Import Tactics Tactics.fwd Eqb.
Import ListNotations.
Import node.

Section Distributed.
  Context `{params : datalog_params}.
  Context {node : nodeT} {node_eqb : Eqb node} {node_eqb_ok : Eqb_ok node_eqb} {node_finite : Fin.Fin node}.
  Context (graph_prog : node -> program).
  Context (Hmrv : forall n, program.meta_rules_valid (graph_prog n)).
  Context (is_input : rel -> bool).
  Context (Hp_good : forall n, Forall (fun R => is_input R = false) (program.concl_rels (graph_prog n))).

  #[local] Instance sender_label : sender_labelT := source.

  Definition rel_forward (d : destn) (R : rel) : bool :=
    match d with
    | output_destn => true (*TODO: don't output everything*)
    | node_destn nd => inb R (program.hyp_rels (graph_prog nd))
    end.

  Definition forward (s : source) (d : destn) (f : message) :=
    rel_forward d (message.rel f).

  Lemma forward_rel_level s d f g :
    message.rel f = message.rel g -> forward s d f = forward s d g.
  Proof. intros. cbv [forward]. congruence. Qed.

  Definition sends (R : rel) (s : source) : bool :=
    match s with
    | input_source => is_input R
    | node_source n => inb R (program.normal_concl_rels (graph_prog n))
    end.

  Definition R_senders (R : rel) : list source := filter (sends R) (Fin.all _).

  Lemma R_senders_NoDup R : NoDup (R_senders R).
  Proof. apply NoDup_filter, Fin.all_NoDup. Qed.

  Lemma node_sends_concl_rels k R :
    In R (program.normal_concl_rels (graph_prog k)) ->
    In (node_source k) (R_senders R).
  Proof. intros HR. apply filter_In. split; [ apply Fin.all_Full | apply inb_true_iff, HR ]. Qed.

  Lemma node_sends_concl_rels_inv k R :
    In (node_source k) (R_senders R) ->
    In R (program.normal_concl_rels (graph_prog k)).
  Proof. intros Hin. apply filter_In in Hin. destruct Hin as [_ Hin]. apply inb_true_iff, Hin. Qed.

  Local Abbreviation nallowed := (node.safe_inputs R_senders).

  Lemma meta_locate pat ojs n cnt :
    (forall s, safe_output R_senders s (ojs s)) ->
    In (message.done_with pat n cnt) (flat_map ojs (Fin.all _)) ->
    In (message.done_with pat n cnt) (ojs n) /\ Existsn_le (message.matches pat) cnt (ojs n).
  Proof.
    intros HF Hin. apply in_flat_map in Hin. destruct Hin as (k & _ & Hin).
    destruct (HF k) as (Hall & _). specialize (Hall _ _ _ Hin). fwd. auto.
  Qed.

  Lemma no_R_matches_off_senders pat ojs n :
    (forall s, safe_output R_senders s (ojs s)) ->
    ~ In n (R_senders pat.(fact_pattern.rel)) ->
    Forall (fun f => ~ message.matches pat f) (ojs n).
  Proof.
    intros HF Hnin. apply Forall_forall. intros f Hf Hmatch. apply Hnin.
    destruct f as [nf |]; [| destruct Hmatch]. destruct (HF n) as (_ & Hsend).
    destruct Hmatch as (Hrel & _). rewrite Hrel. exact (Hsend _ Hf).
  Qed.

  Lemma allowed_of_outputs ojs :
    (forall s, safe_output R_senders s (ojs s)) -> nallowed (flat_map ojs (Fin.all _)).
  Proof.
    intros HF pat ems Hems.
    apply Existsn_le_flat_map_filter with (p := sends pat.(fact_pattern.rel)).
    - intros k _ Hk. apply no_R_matches_off_senders; [ assumption | ].
      intros Hin. apply filter_In in Hin. destruct Hin. congruence.
    - apply Existsn_le_flat_map. eapply Forall2_impl; [ exact Hems | ].
      intros k e Hin. eapply meta_locate in Hin; [ | eassumption ]. fwd. assumption.
  Qed.

  Lemma allowed_of_safe_inputs d inps :
    Graph2WithIO.safe_inputs forward (safe_output R_senders) d inps -> nallowed inps.
  Proof.
    intros (ojs & Hsafe & Hperm) pat ems Hems.
    eapply Existsn_le_perm; [ symmetry; exact Hperm | ].
    apply allowed_of_outputs with (ojs := fun s => filter (forward s d) (ojs s)).
    - intros s. eapply safe_output_mono; [ apply Hsafe | apply filter_submultiset ].
    - eapply Forall2_impl; [ exact Hems | ]. intros. eapply Permutation.Permutation_in; eassumption.
  Qed.

  Lemma In_R_senders R s : In s (R_senders R) <-> sends R s = true.
  Proof. cbv [R_senders]. rewrite filter_In. pose proof (Fin.all_Full s). tauto. Qed.

  Local Abbreviation decomposes := (decomposes forward claim.interp_conj (safe_output R_senders)).

  Lemma decomposes_impl ojs d Q1 Q2 :
    decomposes ojs d Q1 ->
    (forall inps, Q1 inps -> Q2 inps) ->
    decomposes ojs d Q2.
  Proof. intros (Pjs & HPjs & Hsuff) HQ. exists Pjs. split; [ exact HPjs | ]. auto. Qed.

  Lemma decomposes_and ojs d Q1 Q2 :
    decomposes ojs d Q1 ->
    decomposes ojs d Q2 ->
    decomposes ojs d (fun inps => Q1 inps /\ Q2 inps).
  Proof.
    cbv [Graph2WithIO.decomposes claim.interp_conj]. intros (Pjs1 & H1 & Hsuff1) (Pjs2 & H2 & Hsuff2).
    exists (fun s => Pjs1 s ++ Pjs2 s). split.
    - intros s. rewrite Forall_app. auto.
    - intros ojs' Hojs'. split.
      + apply Hsuff1. intros s. destruct (Hojs' s) as [Hs Hsafe]. rewrite Forall_app in Hs. tauto.
      + apply Hsuff2. intros s. destruct (Hojs' s) as [Hs Hsafe]. rewrite Forall_app in Hs. tauto.
  Qed.

  Lemma decomposes_Forall {A} ojs d (Q : A -> list message -> Prop) xs :
    Forall (fun x => decomposes ojs d (Q x)) xs ->
    decomposes ojs d (fun inps => Forall (fun x => Q x inps) xs).
  Proof.
    induction 1 as [ | x xs Hx _ IH ].
    - exists (fun _ => []). split; intros; constructor.
    - eapply decomposes_impl.
      + apply decomposes_and; [ exact Hx | exact IH ].
      + intros inps [? ?]. constructor; assumption.
  Qed.

  Lemma decomposes_normal ojs d nf :
    In (message.normal nf) (inputs_of_outputs forward ojs d) ->
    decomposes ojs d (fun inps => In (message.normal nf) inps).
  Proof.
    intros Hin. apply In_inputs_of_outputs in Hin. destruct Hin as (s & Hin & Hfw).
    exists (fun s' => if eqb s s' then [fact.normal nf] else []). split.
    - intros s'. destr (eqb s s').
      + constructor; [ exact Hin | constructor ].
      + constructor.
    - intros ojs' Hojs'. destruct (Hojs' s) as [Hs _]. rewrite_true (eqb s s) in Hs by reflexivity.
      apply Forall_inv in Hs. apply In_inputs_of_outputs. eauto.
  Qed.

  Lemma sender_counts_of_inputs ojs d pat es :
    (forall s, safe_output R_senders s (ojs s)) ->
    Forall2 (fun s e => In (message.done_with pat s e) (inputs_of_outputs forward ojs d))
      (R_senders pat.(fact_pattern.rel)) es ->
    Existsn (message.matches pat) (list_sum es) (inputs_of_outputs forward ojs d) ->
    forall s,
      In s (R_senders pat.(fact_pattern.rel)) ->
      exists e,
        In (message.done_with pat s e) (ojs s) /\
          rel_forward d pat.(fact_pattern.rel) = true /\
          Existsn_ge (message.matches pat) e (ojs s).
  Proof.
    intros Hsafe Hdone Hnum.
    assert (Hsafef : forall s, safe_output R_senders s (filter (forward s d) (ojs s))).
    { intros s. eapply safe_output_mono; [ apply Hsafe | apply filter_submultiset ]. }
    assert (Hle : Forall2 (fun s e =>
                              In (message.done_with pat s e) (filter (forward s d) (ojs s)) /\
                                Existsn_le (message.matches pat) e (filter (forward s d) (ojs s)))
                    (R_senders pat.(fact_pattern.rel)) es).
    { eapply Forall2_impl; [ exact Hdone | ]. intros s e Hin.
      apply (meta_locate _ (fun s => filter (forward s d) (ojs s))); assumption. }
    assert (Hge : Forall2 (fun s e => Existsn_ge (message.matches pat) e (filter (forward s d) (ojs s)))
                    (R_senders pat.(fact_pattern.rel)) es).
    { apply Existsn_squeeze_flat_map_filter.
      - intros s _ Hs. apply (no_R_matches_off_senders _ (fun s => filter (forward s d) (ojs s))).
        + exact Hsafef.
        + rewrite In_R_senders. congruence.
      - exact Hnum.
      - eapply Forall2_impl; [ exact Hle | ]. intros s e [_ H]. exact H. }
    intros s Hs.
    destruct (Forall2_In_l _ _ _ _ (Forall2_and _ _ _ _ Hle Hge) Hs) as (e & _ & (Hin & _) & Hge_s).
    apply filter_In in Hin. destruct Hin as [Hin Hfw]. exists e. ssplit.
    - exact Hin.
    - exact Hfw.
    - eapply Existsn_ge_submultiset; [ exact Hge_s | apply filter_submultiset ].
  Qed.

  Lemma inputs_count_of_senders ojs d pat ns :
    (forall s, safe_output R_senders s (ojs s)) ->
    Forall2 (fun s n => rel_forward d pat.(fact_pattern.rel) = true /\
                          Existsn (message.matches pat) n (ojs s))
      (R_senders pat.(fact_pattern.rel)) ns ->
    Existsn (message.matches pat) (list_sum ns) (inputs_of_outputs forward ojs d).
  Proof.
    intros Hsafe Hns. apply Existsn_flat_map_filter with (p := sends pat.(fact_pattern.rel)).
    - intros s _ Hs. apply (no_R_matches_off_senders _ (fun s => filter (forward s d) (ojs s))).
      + intros s'. eapply safe_output_mono; [ apply Hsafe | apply filter_submultiset ].
      + rewrite In_R_senders. congruence.
    - apply Existsn_flat_map. eapply Forall2_impl; [ exact Hns | ]. intros s n [Hfw Hn].
      apply Existsn_filter; [ | exact Hn ]. intros [nf | ] Hm; [ | destruct Hm ].
      destruct Hm as [Hrel _]. cbv [forward]. cbn [message.rel]. rewrite <- Hrel. exact Hfw.
  Qed.

  Lemma decomposes_meta ojs d mf :
    (forall s, safe_output R_senders s (ojs s)) ->
    knows_meta_fact R_senders (inputs_of_outputs forward ojs d) mf ->
    decomposes ojs d (fun inps => knows_meta_fact R_senders inps mf).
  Proof.
    intros Hsafe (num & (es & Hdone & ->) & Hnum & Hcons). cbv [meta_fact.rel] in *.
    pose proof (sender_counts_of_inputs _ _ _ _ Hsafe Hdone Hnum) as Hsend.
    exists (fun s => if sends mf.(meta_fact.pattern).(fact_pattern.rel) s
             then [fact.meta (sent_meta_fact (ojs s) mf.(meta_fact.pattern))] else []).
    split.
    - intros s. destruct (sends _ s) eqn:Hs; [ | constructor ].
      rewrite <- In_R_senders in Hs. destruct (Hsend s Hs) as (e & Hin & _ & Hge).
      constructor; [ | constructor ]. eapply interp_sent_meta_fact; eassumption.
    - intros ojs' Hojs'.
      assert (Hsend' : forall s,
                 In s (R_senders mf.(meta_fact.pattern).(fact_pattern.rel)) ->
                 exists n',
                   In (message.done_with mf.(meta_fact.pattern) s n') (ojs' s) /\
                     rel_forward d mf.(meta_fact.pattern).(fact_pattern.rel) = true /\
                     Existsn (message.matches mf.(meta_fact.pattern)) n' (ojs' s) /\
                     meta_fact.consistent_with (sent_meta_fact (ojs s) mf.(meta_fact.pattern))
                       (knows_normal_fact (ojs' s))).
      { intros s Hs. destruct (Hsend s Hs) as (_ & _ & Hfw & _).
        rewrite In_R_senders in Hs. destruct (Hojs' s) as [Hc Hsafe']. rewrite Hs in Hc.
        apply Forall_inv in Hc. destruct (interp_meta_safe _ _ _ _ Hc Hsafe') as (n' & Hin & Hn' & Hcons').
        exists n'. ssplit; assumption. }
      pose proof (proj2 (Forall_forall _ _) Hsend') as Hns'.
      apply Forall_exists_r_Forall2 in Hns'. destruct Hns' as (ns' & Hns').
      exists (list_sum ns'). ssplit.
      + exists ns'. split; [ | reflexivity ].
        eapply Forall2_impl; [ exact Hns' | ]. intros s n' (Hin & Hfw & _).
        apply In_inputs_of_outputs. eauto.
      + apply inputs_count_of_senders; [ apply Hojs' | ].
        eapply Forall2_impl; [ exact Hns' | ]. intros s n' (_ & Hfw & Hn' & _). split; assumption.
      + intros nf Hm. rewrite (Hcons nf Hm). cbv [knows_normal_fact]. rewrite !In_inputs_of_outputs.
        assert (Hagree : forall s, In (message.normal nf) (ojs s) <-> In (message.normal nf) (ojs' s)).
        { intros s. destruct (sends mf.(meta_fact.pattern).(fact_pattern.rel) s) eqn:Hs.
          - rewrite <- In_R_senders in Hs. destruct (Hsend' s Hs) as (n' & _ & _ & _ & Hcons').
            exact (meta_fact.consistent_with_iff _ _ _ _ (sent_meta_fact_consistent _ _) Hcons' Hm).
          - assert (Hns : ~ In s (R_senders mf.(meta_fact.pattern).(fact_pattern.rel)))
              by (rewrite In_R_senders; congruence).
            split; intros Hin; exfalso; apply Hns.
            + eapply safe_output_sender; [ apply Hsafe | exact Hin | exact Hm ].
            + eapply safe_output_sender; [ apply Hojs' | exact Hin | exact Hm ]. }
        setoid_rewrite Hagree. reflexivity.
  Qed.

  Lemma decomposes_knows_fact ojs d h :
    (forall s, safe_output R_senders s (ojs s)) ->
    knows_fact R_senders (inputs_of_outputs forward ojs d) h ->
    decomposes ojs d (fun inps => knows_fact R_senders inps h).
  Proof.
    intros Hsafe Hh. destruct h as [nf | mf].
    - apply decomposes_normal. exact Hh.
    - apply decomposes_meta; assumption.
  Qed.

  Lemma can_claim_conj_decomposes prog ojs d Ps :
    (forall s, safe_output R_senders s (ojs s)) ->
    can_claim_conj R_senders prog (inputs_of_outputs forward ojs d) Ps ->
    decomposes ojs d (fun inps => can_claim_conj R_senders prog inps Ps).
  Proof.
    intros Hsafe HPs. apply decomposes_Forall. eapply Forall_impl; [ exact HPs | ].
    intros P (hyps & Hstep & Hhyps).
    apply decomposes_impl with (Q1 := fun inps => Forall (knows_fact R_senders inps) hyps).
    - apply decomposes_Forall. eapply Forall_impl; [ exact Hhyps | ].
      intros h Hh. apply decomposes_knows_fact; assumption.
    - intros inps Hk. exists hyps. split; assumption.
  Qed.

  Definition graph_sat :=
    graph_sat forward claim.interp_conj (fun n => can_claim_conj R_senders (graph_prog n)) (safe_output R_senders).

  Definition graph_step :=
    graph_step forward (fun n => step R_senders (graph_prog n) (node_source n)).

  Lemma distributed_graph_sat_sound loc P t gs :
    star graph_step (init_graph_state (fun _ => init)) t gs ->
    safe_output R_senders input_source (flat_map inputs_of t) ->
    graph_sat (flat_map inputs_of t) loc P ->
    eventually (will_step graph_step (safe_output R_senders input_source)) (fun '(gs', t') => claim.interp_conj loc P (outputs_at gs' t' loc)) (gs, t).
  Proof.
    intros. eapply graph_sat_sound; try eassumption.
    - intros n s m. eexists. apply input_step.
    - apply claim.interp_conj_mono.
    - intros n. apply safe_output_mono.
    - intros n. split; intros; contradiction.
    - intros. eapply safe_preserved; try eassumption.
      intros. apply node_sends_concl_rels. assumption.
    - intros. eapply eventually_will_step_weaken_allowed.
      + eapply can_claim_conj_sound; try eassumption.
        * apply Hmrv.
        * eapply allowed_of_safe_inputs; eassumption.
      + apply allowed_of_safe_inputs.
    - intros. cbv beta in *. eapply can_claim_conj_mono_inc; try eassumption.
      eapply allowed_of_safe_inputs; eassumption.
  Qed.

  Lemma distributed_graph_sat_complete t gs loc P :
    star graph_step (init_graph_state (fun _ => init)) t gs ->
    safe_output R_senders input_source (flat_map inputs_of t) ->
    claim.interp_conj loc P (outputs_at gs t loc) ->
    graph_sat (flat_map inputs_of t) loc P.
  Proof.
    intros. eapply graph_sat_complete; try eassumption.
    - apply claim.interp_conj_mono.
    - intros n. apply safe_output_mono.
    - intros n. split; intros; contradiction.
    - intros. cbv beta in *. eapply safe_preserved; try eassumption.
      intros. apply node_sends_concl_rels. assumption.
    - intros. cbv beta in *. eapply can_claim_conj_complete; try eassumption.
      + apply Hmrv.
      + eapply allowed_of_safe_inputs; eassumption.
    - intros. apply can_claim_conj_decomposes; assumption.
    - intros. cbv beta in *. eapply can_claim_conj_mono_inc; try eassumption.
      eapply allowed_of_safe_inputs; eassumption.
  Qed.

End Distributed.
