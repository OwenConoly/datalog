From Stdlib Require Import List PeanoNat Lia.
From Datalog Require Import Datalog Graph Node Operational List Tactics.
From coqutil Require Import Map.Interface Datatypes.List.
Import ListNotations.

Section __.
  Context {rel : relT} {exprvar : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T}.
  Context {context : map.map exprvar T} {context_ok : map.ok context}.
  Context (is_input : rel -> bool).
  Context (p : prog).
  Context (Hmeta_rules : meta_rules_valid (rules_of p)).
  Context (Hp_input : Forall (good_non_meta_rule is_input) p.(non_meta_rules)).
  Context (Hp_meta_input : Forall (good_meta_rule_inputs is_input) p.(meta_rules)).
  Context (Hfin : meta_facts_finite p).
  Context (Hlen : 0 < length p.(non_meta_rules)).

  Local Notation R_senders := (Operational.R_senders is_input p).
  Local Notation rules_of := (Operational.rules_of p).
  Local Notation knows_datalog_fact := (Node.knows_datalog_fact R_senders).
  Local Notation good_input_facts := (Operational.good_input_facts is_input).
  Local Notation state_correct := (Operational.state_correct is_input p).
  Local Notation state_complete := (Operational.state_complete is_input p).
  Local Notation sane_state := (Operational.sane_state is_input p).
  Local Notation meta_facts_correct := (Operational.meta_facts_correct is_input p).
  Local Notation meta_facts_ok := (Operational.meta_facts_ok is_input p).
  Local Notation has_derived_datalog_fact := (Operational.has_derived_datalog_fact is_input p).

  Definition start (inputs : list dfact) : state :=
    {| known_facts := inputs; sents := repeat [] (length p.(non_meta_rules)) |}.

  Lemma good_input_no_node_meta (inputs : list dfact) R a n num :
    good_input_facts inputs -> ~ In (meta_dfact R a (node_source n) num) inputs.
  Proof.
    intros [Hall _] Hin. rewrite Forall_forall in Hall.
    specialize (Hall _ Hin). cbn in Hall. discriminate.
  Qed.

  Lemma mfc_start (inputs : list dfact) : meta_facts_correct (start inputs).
  Proof.
    unfold meta_facts_correct, start. cbn [known_facts sents]. rewrite repeat_length.
    apply Forall3_repeat_2. eapply Forall2_impl.
    - apply Forall2_true. rewrite length_seq. reflexivity.
    - intros r n _ R mf_args num Hin. destruct Hin.
  Qed.

  Lemma mfok_start (inputs : list dfact) : meta_facts_ok (start inputs).
  Proof.
    unfold meta_facts_ok, start. cbn [known_facts sents]. rewrite repeat_length.
    apply Forall3_repeat_2. eapply Forall2_impl.
    - apply Forall2_true. rewrite length_seq. reflexivity.
    - intros r n _ mf_rel mf_args num Hin. destruct Hin.
  Qed.

  Lemma sane_start (inputs : list dfact) :
    good_input_facts inputs -> sane_state inputs (start inputs).
  Proof.
    intros Hg. unfold start. constructor; cbn [known_facts sents].
    - apply repeat_length.
    - intros R a num H. exact H.
    - intros R a n num H. exfalso. exact (good_input_no_node_meta inputs R a n num Hg H).
    - intros R a. destruct (Existsn_total (dfact_matches R a) inputs) as (nk & Hnk).
      exists (repeat 0 (length p.(non_meta_rules))), nk, nk. split; [| split; [| split]].
      + apply Forall2_repeat. constructor.
      + exact Hnk.
      + exact Hnk.
      + rewrite list_sum_repeat. lia.
    - intros R HER. split.
      + intros a. apply Forall_repeat. constructor.
      + intros a n num. exact (good_input_no_node_meta inputs R a n num Hg).
    - intros g H. exact H.
  Qed.

  Lemma sc_start (inputs : list dfact) :
    good_input_facts inputs -> state_correct inputs (start inputs).
  Proof.
    intros Hg f (Hd & Hmc). destruct f as [R args | R mf_args mf_set].
    - cbv [has_derived_datalog_fact] in Hd. unfold start in Hd. cbn [known_facts] in Hd.
      apply prog_impl_leaf. cbn [Node.knows_datalog_fact]. exact Hd.
    - cbv [has_derived_datalog_fact] in Hd. cbv [mf_consistent_state] in Hmc.
      unfold start in Hd, Hmc. cbn [known_facts] in Hd, Hmc.
      destruct (is_input R) eqn:HER.
      + apply prog_impl_leaf. cbn [Node.knows_datalog_fact].
        destruct Hd as (num & Hin & Hexn). exists num. split; [| split].
        * rewrite expect_num_R_facts_eq, HER. exact Hin.
        * exact Hexn.
        * intros nfa Hm. exact (Hmc nfa Hm).
      + exfalso. destruct (Hd 0 Hlen) as (num & Hin).
        exact (good_input_no_node_meta inputs R mf_args 0 num Hg Hin).
  Qed.

  Lemma start_INV (inputs : list dfact) :
    good_input_facts inputs ->
    sane_state inputs (start inputs) /\
    meta_facts_correct (start inputs) /\
    meta_facts_ok (start inputs) /\
    state_correct inputs (start inputs).
  Proof.
    intros Hg.
    split; [apply sane_start; exact Hg |].
    split; [apply mfc_start |].
    split; [apply mfok_start | apply sc_start; exact Hg].
  Qed.

  Theorem prog_impl_iff_comp_step (inputs : list dfact) (f : fact) :
    good_input_facts inputs ->
    (prog_impl rules_of (knows_datalog_fact inputs) f <->
     exists s', (comp_step is_input p)^* (start inputs) s' /\
                has_derived_datalog_fact s' f /\ mf_consistent_state s' f).
  Proof.
    intros Hg.
    destruct (start_INV inputs Hg) as (Hsane & Hmfc & Hmfok & Hsc).
    split.
    - intros Hprog.
      assert (Hcompl : state_complete inputs (start inputs))
        by (apply comp_step_complete; assumption).
      destruct (Hcompl _ Hprog) as (s' & Hsteps & Hderiv).
      assert (Hsc' : state_correct inputs s')
        by (eapply comp_steps_sound; eassumption).
      exists s'. split; [exact Hsteps | split; [exact Hderiv |]].
      eapply correct_impl_consistent; eassumption.
    - intros (s' & Hsteps & Hderiv & Hcons).
      assert (Hsc' : state_correct inputs s')
        by (eapply comp_steps_sound; eassumption).
      apply Hsc'. split; [exact Hderiv | exact Hcons].
  Qed.

End __.
