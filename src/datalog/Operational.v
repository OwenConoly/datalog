From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Classical_Prop.
From Stdlib Require Import Relations.Relation_Operators Relations.Operators_Properties.

From Datalog Require Import Map Tactics List Pftree Relations Datalog.

From coqutil Require Import Map.Interface Map.Properties Tactics Tactics.fwd Datatypes.List Eqb.

Import ListNotations.

Module op_source.
  Section __.
    Context `{params : datalog_params}.

    Variant op_source :=
      | rule (r : rule)
      | input.
  End __.
End op_source. Abbreviation op_source := op_source.op_source.

Module op_message.
  Section __.
    Context `{params : datalog_params}.

    Variant op_message :=
      | normal (nf : normal_fact) (src : op_source)
      | done_with (pat : fact_pattern) (src : op_source).
  End __.
End op_message. Abbreviation op_message := op_message.op_message.

Section __.
  Context `{params : datalog_params}.
  Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.

  Context (is_input : rel -> bool).

  Context (p : program).

  Definition normal_args_with (R : rel) (m : op_message) : option (list value) :=
    match m with
    | op_message.normal nf _ =>
        if eqb R nf.(normal_fact.rel) then Some nf.(normal_fact.args) else None
    | op_message.done_with _ _ => None
    end.

  Lemma In_normal_args_with R ms args :
    In args (filter_map (normal_args_with R) ms) <->
    exists src, In (op_message.normal {| normal_fact.rel := R; normal_fact.args := args |} src) ms.
  Proof.
    rewrite in_filter_map. split.
    - intros ([nf src | ] & Hin & Hargs); [|discriminate].
      destruct nf as [nrel nargs]. cbv [normal_args_with] in Hargs. simpl in Hargs.
      destr (eqb R nrel); [|discriminate]. invert Hargs. eauto.
    - intros (src & Hin). eexists. split; [eassumption|]. cbv [normal_args_with].
      rewrite eqb_refl_true by assumption. reflexivity.
  Qed.

  Definition all_done_with known pat :=
    if is_input pat.(fact_pattern.rel) then
      In (op_message.done_with pat op_source.input) known
    else
      Forall (fun r => In (op_message.done_with pat (op_source.rule r)) known) p.(program.rules).

  Definition op_can_deduce_pattern known pat :=
    exists mr pats,
      In mr p.(program.meta_rules) /\
        meta_rule.pattern_interp mr pat pats /\
        Forall (all_done_with known) pats.

  Definition meta_facts_correct_at_rule (known : list op_message) r :=
    forall pat,
      In (op_message.done_with pat (op_source.rule r)) known ->
      exists mr pats,
        In mr p.(program.meta_rules) /\
          meta_rule.pattern_interp mr pat pats /\
          Forall (all_done_with known) pats /\
          ~In pat pats.

  Definition meta_facts_correct (known : list op_message) :=
    Forall (meta_facts_correct_at_rule known) p.(program.rules).

  Definition op_knows_normal_fact known nf :=
    exists src, In (op_message.normal nf src) known.

  Definition op_knows_meta_fact known mf :=
    all_done_with known mf.(meta_fact.pattern) /\
      meta_fact.consistent_with mf (op_knows_normal_fact known).

  Definition op_knows_fact known f :=
    match f with
    | fact.normal nf => op_knows_normal_fact known nf
    | fact.meta mf => op_knows_meta_fact known mf
    end.

  Definition op_can_deduce_normal_fact r known nf :=
    exists hyps,
      rule.interp r nf hyps /\ Forall (op_knows_fact known) hyps.

  Definition ok_to_deduce (r : rule) known (pat : fact_pattern) :=
    forall nf,
      op_can_deduce_normal_fact r known nf ->
      fact_pattern.matches pat nf ->
      In (op_message.normal nf (op_source.rule r)) known.

  Definition meta_facts_ok_at_rule known r :=
    forall pat,
      In (op_message.done_with pat (op_source.rule r)) known ->
      ok_to_deduce r known pat.

  Definition meta_facts_ok known :=
    Forall (meta_facts_ok_at_rule known) p.(program.rules).

  Definition can_deduce_message (r : rule) known (f : op_message) : Prop :=
    match f with
    | op_message.normal nf src =>
        src = op_source.rule r /\
          op_can_deduce_normal_fact r known nf
    | op_message.done_with pat src =>
        src = op_source.rule r /\
          ok_to_deduce r known pat /\
          op_can_deduce_pattern known pat
    end.

  Definition comp_step (s : list op_message) (s' : list op_message) :=
    exists new_fact r,
      In r p.(program.rules) /\
        can_deduce_message r s new_fact /\
        s' = new_fact :: s.

  Definition is_input_fact (f : op_message) :=
    match f with
    | op_message.normal nf op_source.input => is_input nf.(normal_fact.rel)
    | op_message.done_with pat op_source.input => is_input pat.(fact_pattern.rel)
    | op_message.normal _ (op_source.rule _) | op_message.done_with _ (op_source.rule _) => false
    end.

  Context (Hmeta_rules : program.meta_rules_valid p).

  Context (Hp_good : Forall (fun R => is_input R = false) (program.concl_rels p)).

  Context (Hrules : 0 < length p.(program.rules)).

  Lemma concl_rel_not_input R :
    In R (program.concl_rels p) -> is_input R = false.
  Proof. rewrite Forall_forall in Hp_good. auto. Qed.

  Definition good_input_facts input_facts :=
    Forall (fun f => is_input_fact f = true) input_facts.

  Record sane_state {input_facts known : list op_message} : Prop := {
    sane_inputs_known : incl input_facts known;
    sane_meta_facts_correct : meta_facts_correct known;
    sane_meta_facts_ok : meta_facts_ok known;
  }.

  Arguments sane_state : clear implicits.

  Lemma rule_concl_not_input r nf hyps :
    In r p.(program.rules) ->
    rule.interp r nf hyps ->
    is_input nf.(normal_fact.rel) = false.
  Proof.
    intros. apply concl_rel_not_input.
    eauto using program.rule_concl_rel_in, rule.interp_concl_relname_in.
  Qed.

  Lemma can_deduce_implies_not_input r known nf :
    In r p.(program.rules) ->
    op_can_deduce_normal_fact r known nf ->
    is_input nf.(normal_fact.rel) = false.
  Proof. intros Hr (hyps & Hri & _). eauto using rule_concl_not_input. Qed.

  Lemma pattern_concl_not_input mr pat pats :
    In mr p.(program.meta_rules) ->
    meta_rule.pattern_interp mr pat pats ->
    is_input pat.(fact_pattern.rel) = false.
  Proof.
    intros. apply concl_rel_not_input.
    eauto using program.meta_rule_concl_rel_in,
      meta_rule.pattern_interp_concl_relname_in.
  Qed.

  Lemma comp_step_incl s s' :
    comp_step s s' -> incl s s'.
  Proof. cbv [comp_step]. intros. fwd. auto with incl. Qed.

  Lemma comp_steps_incl s s' :
    comp_step^* s s' -> incl s s'.
  Proof. induction 1; eauto using incl_refl, incl_tran, comp_step_incl. Qed.

  Lemma all_done_with_incl k1 k2 pat :
    incl k1 k2 -> all_done_with k1 pat -> all_done_with k2 pat.
  Proof.
    cbv [all_done_with]. intros Hincl. destruct (is_input _); [auto|].
    intros H. eapply Forall_impl; [exact H|]. auto.
  Qed.

  Lemma all_done_with_cons_done known pat src q :
    q <> pat ->
    all_done_with (op_message.done_with pat src :: known) q ->
    all_done_with known q.
  Proof.
    cbv [all_done_with]. intros Hne. destruct (is_input _).
    - intros [Heq | H]; [invert Heq; congruence | assumption].
    - intros H. eapply Forall_impl; [exact H|].
      intros r [Heq | ?]; [invert Heq; congruence | assumption].
  Qed.

  Lemma op_can_deduce_pattern_incl k1 k2 pat :
    incl k1 k2 -> op_can_deduce_pattern k1 pat -> op_can_deduce_pattern k2 pat.
  Proof.
    intros Hincl (mr & pats & Hmr & Hpi & Hdone). exists mr, pats. ssplit; try assumption.
    eapply Forall_impl; [exact Hdone|]. eauto using all_done_with_incl.
  Qed.

  Lemma can_deduce_pattern_not_input known pat :
    op_can_deduce_pattern known pat -> is_input pat.(fact_pattern.rel) = false.
  Proof. intros (mr & pats & Hmr & Hpi & _). eauto using pattern_concl_not_input. Qed.

  Lemma op_knows_normal_fact_incl k1 k2 nf :
    incl k1 k2 -> op_knows_normal_fact k1 nf -> op_knows_normal_fact k2 nf.
  Proof. intros Hincl (src & Hin). exists src. auto. Qed.

  Lemma step_no_new_matches known known' pat nf :
    meta_facts_ok known ->
    comp_step known known' ->
    all_done_with known pat ->
    fact_pattern.matches pat nf ->
    op_knows_normal_fact known' nf ->
    op_knows_normal_fact known nf.
  Proof.
    intros Hok Hstep Hdone Hm (src & Hin). pose proof Hstep as (m & r & Hr & Hcan & ->).
    destruct Hin as [-> | Hin]; [| exists src; assumption]. destruct Hcan as (-> & Hcan).
    cbv [all_done_with] in Hdone.
    rewrite (proj1 Hm), (can_deduce_implies_not_input _ _ _ Hr Hcan) in Hdone.
    cbv [meta_facts_ok meta_facts_ok_at_rule] in Hok.
    rewrite Forall_forall in Hdone, Hok. eexists. apply (Hok _ Hr _ (Hdone _ Hr)); assumption.
  Qed.

  Lemma knows_step_down known known' q h :
    meta_facts_ok known ->
    comp_step known known' ->
    all_done_with known q ->
    fact.covered_by h q ->
    op_knows_fact known' h ->
    op_knows_fact known h.
  Proof.
    intros Hok Hstep Hdone Hcov. pose proof (comp_step_incl _ _ Hstep) as Hincl.
    destruct h as [nf | mf]; cbv [fact.covered_by] in Hcov.
    - cbv [op_knows_fact]. eauto using step_no_new_matches.
    - subst q. cbv [op_knows_fact op_knows_meta_fact meta_fact.consistent_with].
      intros (_ & Hcons). split; [assumption|].
      intros nf Hm. rewrite Hcons by assumption.
      split; eauto using step_no_new_matches, op_knows_normal_fact_incl.
  Qed.

  Lemma ok_to_deduce_step r known known' pat :
    In r p.(program.rules) ->
    meta_facts_ok known ->
    comp_step known known' ->
    op_can_deduce_pattern known pat ->
    ok_to_deduce r known pat ->
    ok_to_deduce r known' pat.
  Proof.
    intros Hr Hok Hstep (mr & pats & Hmr & Hpi & Hdone) Hok_r nf (hyps & Hri & Hknown) Hm.
    apply (comp_step_incl _ _ Hstep). apply Hok_r; [|assumption].
    exists hyps. split; [assumption|].
    pose proof (Hmeta_rules _ _ Hmr Hr _ _ _ _ Hpi Hri Hm) as Hcov.
    eapply Forall_impl; [apply Forall_and; [exact Hcov | exact Hknown]|].
    simpl. intros h (Hcov_h & Hk_h). apply Exists_exists in Hcov_h. fwd.
    rewrite Forall_forall in Hdone. eauto using knows_step_down.
  Qed.

  Lemma step_preserves_meta_facts_correct known known' :
    meta_facts_correct known ->
    comp_step known known' ->
    meta_facts_correct known'.
  Proof.
    intros Hmfc Hstep. pose proof (comp_step_incl _ _ Hstep) as Hincl.
    pose proof Hstep as (m & r & Hr & Hcan & ->).
    cbv [meta_facts_correct meta_facts_correct_at_rule] in Hmfc |- *.
    rewrite Forall_forall in Hmfc |- *. intros r0 Hr0 pat Hin.
    destruct (classic (In (op_message.done_with pat (op_source.rule r0)) known)) as [Hold | Hnew].
    - destruct (Hmfc _ Hr0 _ Hold) as (mr & pats & Hmr & Hpi & Hdone & Hnotin).
      exists mr, pats. ssplit; try assumption.
      eapply Forall_impl; [exact Hdone|]. eauto using all_done_with_incl.
    - destruct Hin as [Heq | Hin]; [|contradiction]. subst m.
      cbv [can_deduce_message] in Hcan. destruct Hcan as (Heq & _ & (mr & pats & Hmr & Hpi & Hdone)).
      invert Heq. exists mr, pats. ssplit; try assumption.
      + eapply Forall_impl; [exact Hdone|]. eauto using all_done_with_incl.
      + intros Hin_pat. apply Hnew. rewrite Forall_forall in Hdone. specialize (Hdone _ Hin_pat).
        cbv [all_done_with] in Hdone. rewrite (pattern_concl_not_input _ _ _ Hmr Hpi) in Hdone.
        rewrite Forall_forall in Hdone. auto.
  Qed.

  Lemma step_preserves_meta_facts_ok known known' :
    meta_facts_correct known ->
    meta_facts_ok known ->
    comp_step known known' ->
    meta_facts_ok known'.
  Proof.
    intros Hmfc Hok Hstep. pose proof Hstep as (m & r & Hr & Hcan & ->).
    pose proof Hok as Hok'.
    cbv [meta_facts_correct meta_facts_correct_at_rule meta_facts_ok meta_facts_ok_at_rule]
      in Hmfc, Hok' |- *.
    rewrite Forall_forall in Hmfc, Hok' |- *. intros r0 Hr0 pat [Heq | Hin].
    - subst m. cbv [can_deduce_message] in Hcan. destruct Hcan as (Heq & Hok_r & Hcdp).
      invert Heq. eauto using ok_to_deduce_step.
    - destruct (Hmfc _ Hr0 _ Hin) as (mr & pats & Hmr & Hpi & Hdone & _).
      eapply ok_to_deduce_step; eauto. exists mr, pats. auto.
  Qed.

  Lemma step_preserves_sane inputs known known' :
    sane_state inputs known ->
    comp_step known known' ->
    sane_state inputs known'.
  Proof.
    intros [Hinp Hmfc Hok] Hstep. constructor.
    - eauto using incl_tran, comp_step_incl.
    - eauto using step_preserves_meta_facts_correct.
    - eauto using step_preserves_meta_facts_ok.
  Qed.

  Lemma steps_preserves_sane inputs known known' :
    sane_state inputs known ->
    comp_step^* known known' ->
    sane_state inputs known'.
  Proof. intros Hsane Hsteps. induction Hsteps; eauto using step_preserves_sane. Qed.

  Definition has_derived_datalog_fact known (f : fact) :=
    match f with
    | fact.normal nf => op_knows_normal_fact known nf
    | fact.meta mf => all_done_with known mf.(meta_fact.pattern)
    end.

  Definition mf_consistent_state known (f : fact) :=
    match f with
    | fact.normal _ => True
    | fact.meta mf => meta_fact.consistent_with mf (op_knows_normal_fact known)
    end.

  Lemma op_knows_fact_iff known f :
    op_knows_fact known f <->
      has_derived_datalog_fact known f /\ mf_consistent_state known f.
  Proof.
    destruct f; cbv [op_knows_fact op_knows_meta_fact has_derived_datalog_fact mf_consistent_state].
    all: tauto.
  Qed.

  Definition state_correct (inputs known : list op_message) :=
    forall f, op_knows_fact known f -> program.interp p (op_knows_fact inputs) f.

  Lemma good_input_set_inputs inputs :
    good_input_facts inputs ->
    program.good_input_set p (op_knows_fact inputs).
  Proof.
    intros Hinp. cbv [good_input_facts] in Hinp. rewrite Forall_forall in Hinp. split.
    - intros [nf | mf] Hf Hconcl; apply concl_rel_not_input in Hconcl;
        cbv [fact.rel meta_fact.rel] in Hconcl.
      + destruct Hf as (src & Hf). apply Hinp in Hf. destruct src; simpl in Hf; congruence.
      + destruct Hf as (Hdone & _). cbv [all_done_with] in Hdone. rewrite Hconcl in Hdone.
        destruct (length_pos_In _ Hrules) as (r & Hr). rewrite Forall_forall in Hdone.
        specialize (Hdone _ Hr). apply Hinp in Hdone. discriminate.
    - intros mf (_ & Hcons). exact Hcons.
  Qed.

  Lemma derived_meta_facts_agree inputs mf1 mf2 :
    good_input_facts inputs ->
    program.interp p (op_knows_fact inputs) (fact.meta mf1) ->
    program.interp p (op_knows_fact inputs) (fact.meta mf2) ->
    meta_fact.agree mf1 mf2.
  Proof.
    intros Hinp. pose proof (good_input_set_inputs _ Hinp) as (Hdisj & Hlie).
    apply program.meta_facts_consistent; eauto using fact.set_doesnt_lie_agree.
  Qed.

  Lemma derived_meta_fact_honest inputs mf :
    good_input_facts inputs ->
    program.interp p (op_knows_fact inputs) (fact.meta mf) ->
    meta_fact.consistent_with mf (fact.normal_subset (program.interp p (op_knows_fact inputs))).
  Proof.
    intros Hinp. apply program.valid_impl_honest; [assumption|].
    apply good_input_set_inputs. assumption.
  Qed.

  Definition known_meta_fact known pat :=
    meta_fact.mk pat (filter_map (normal_args_with pat.(fact_pattern.rel)) known).

  Lemma known_meta_fact_consistent known pat :
    meta_fact.consistent_with (known_meta_fact known pat) (op_knows_normal_fact known).
  Proof.
    intros nf Hm. pose proof Hm as (Hrel & Hargs). cbv [known_meta_fact].
    rewrite meta_fact.contains_mk, In_normal_args_with. destruct nf.
    cbn in Hrel, Hargs |- *. rewrite Hrel. tauto.
  Qed.

  Lemma known_meta_fact_knows known pat :
    all_done_with known pat ->
    op_knows_fact known (fact.meta (known_meta_fact known pat)).
  Proof. split; [assumption | apply known_meta_fact_consistent]. Qed.

  Lemma correct_impl_consistent inputs known f :
    good_input_facts inputs ->
    state_correct inputs known ->
    program.interp p (op_knows_fact inputs) f ->
    has_derived_datalog_fact known f ->
    mf_consistent_state known f.
  Proof.
    intros Hinp Hcorrect Himpl Hderived. destruct f as [nf | mf]; [exact I|].
    cbv [mf_consistent_state]. intros nf Hm.
    pose proof (derived_meta_facts_agree _ _ (known_meta_fact known mf.(meta_fact.pattern)) Hinp Himpl)
      as Hagree.
    rewrite (Hagree (Hcorrect _ (known_meta_fact_knows _ _ Hderived)) nf Hm Hm).
    apply known_meta_fact_consistent. assumption.
  Qed.

  Lemma covered_derivable_known inputs known q h :
    good_input_facts inputs ->
    all_done_with known q ->
    program.interp p (op_knows_fact inputs) (fact.meta (known_meta_fact known q)) ->
    fact.covered_by h q ->
    program.interp p (op_knows_fact inputs) h ->
    op_knows_fact known h.
  Proof.
    intros Hinp Hdone Himpl_q Hcov Himpl.
    destruct h as [nf | mf]; cbv [fact.covered_by] in Hcov.
    - cbv [op_knows_fact]. rewrite <- (known_meta_fact_consistent known q nf Hcov).
      apply (derived_meta_fact_honest _ _ Hinp Himpl_q nf Hcov). exact Himpl.
    - subst q. split; [assumption|]. intros nf Hm.
      rewrite (derived_meta_facts_agree _ _ _ Hinp Himpl Himpl_q nf Hm Hm).
      apply known_meta_fact_consistent. assumption.
  Qed.

  (* Every derivable fact matching [pat] is known once every sender is done with
     [pat]: its rule instance's hypotheses are covered by the patterns of the meta
     rule that justified the done message, whose known meta facts are exact. *)
  Lemma derivable_matches_known inputs known pat nf :
    good_input_facts inputs ->
    meta_facts_correct known ->
    meta_facts_ok known ->
    (forall q, q <> pat -> all_done_with known q ->
               program.interp p (op_knows_fact inputs) (fact.meta (known_meta_fact known q))) ->
    incl inputs known ->
    all_done_with known pat ->
    fact_pattern.matches pat nf ->
    program.interp p (op_knows_fact inputs) (fact.normal nf) ->
    op_knows_normal_fact known nf.
  Proof.
    intros Hinp Hmfc Hok Hqs Hincl Hdone Hm Himpl. invert Himpl.
    - eapply op_knows_normal_fact_incl; eassumption.
    - invert H. apply Exists_exists in H2. destruct H2 as (r & Hr & Hri).
      cbv [all_done_with] in Hdone.
      rewrite (proj1 Hm), (rule_concl_not_input _ _ _ Hr Hri) in Hdone.
      rewrite Forall_forall in Hdone. specialize (Hdone _ Hr).
      cbv [meta_facts_ok meta_facts_ok_at_rule] in Hok. rewrite Forall_forall in Hok.
      eexists. apply (Hok _ Hr _ Hdone); [|assumption].
      cbv [meta_facts_correct meta_facts_correct_at_rule] in Hmfc. rewrite Forall_forall in Hmfc.
      destruct (Hmfc _ Hr _ Hdone) as (mr & pats & Hmr & Hpi & Hdone_pats & Hnotin).
      exists l. split; [assumption|].
      pose proof (Hmeta_rules _ _ Hmr Hr _ _ _ _ Hpi Hri Hm) as Hcov.
      eapply Forall_impl; [apply Forall_and; [exact Hcov | exact H0]|].
      simpl. intros h (Hcov_h & Himpl_h). apply Exists_exists in Hcov_h.
      destruct Hcov_h as (q & Hq & Hcov_h). rewrite Forall_forall in Hdone_pats.
      eapply covered_derivable_known; eauto. apply Hqs; auto. congruence.
  Qed.

  Lemma comp_step_sound inputs known known' :
    good_input_facts inputs ->
    sane_state inputs known ->
    state_correct inputs known ->
    comp_step known known' ->
    state_correct inputs known'.
  Proof.
    intros Hinp Hsane Hcorrect Hstep f Hf. pose proof (comp_step_incl _ _ Hstep) as Hincl.
    pose proof Hstep as (m & r & Hr & Hcan & ->).
    destruct f as [nf | mf].
    - destruct Hf as (src & [-> | Hf]); [| apply Hcorrect; exists src; exact Hf].
      destruct Hcan as (_ & hyps & Hri & Hhyps).
      eapply pftree.step; [constructor; apply Exists_exists; eauto|].
      eapply Forall_impl; [exact Hhyps|]. auto.
    - destruct (classic (all_done_with known mf.(meta_fact.pattern))) as [Hdone | Hnot_done].
      { apply Hcorrect. split; [exact Hdone|].
        destruct Hf as (_ & Hcons). cbv [meta_fact.consistent_with] in Hcons |- *.
        intros nf Hm. rewrite Hcons by assumption.
        split; eauto using step_no_new_matches, sane_meta_facts_ok, op_knows_normal_fact_incl. }
      destruct Hf as (Hdone' & Hcons).
      assert (m = op_message.done_with mf.(meta_fact.pattern) (op_source.rule r)) as ->.
      { destruct m as [nf src | pat src].
        - exfalso. apply Hnot_done. cbv [all_done_with] in Hdone' |- *. destruct (is_input _).
          + destruct Hdone' as [Heq | ?]; [discriminate | assumption].
          + eapply Forall_impl; [exact Hdone'|]. intros r0 [Heq | ?]; [discriminate | assumption].
        - cbv [can_deduce_message] in Hcan. destruct Hcan as (-> & _ & _). f_equal.
          destruct (classic (pat = mf.(meta_fact.pattern))) as [-> | Hne]; [reflexivity | exfalso].
          eauto using all_done_with_cons_done. }
      cbv [can_deduce_message] in Hcan.
      destruct Hcan as (_ & Hok_r & (mr & pats & Hmr & Hpi & Hdone_pats)).
      set (d := op_message.done_with mf.(meta_fact.pattern) (op_source.rule r)) in *.
      pose proof (step_preserves_sane _ _ _ Hsane Hstep) as Hsane'.
      assert (Hqs : forall q, q <> mf.(meta_fact.pattern) -> all_done_with (d :: known) q ->
                              program.interp p (op_knows_fact inputs)
                                (fact.meta (known_meta_fact (d :: known) q))).
      { intros q Hne Hdone_q. change (known_meta_fact (d :: known) q) with (known_meta_fact known q).
        apply Hcorrect. apply known_meta_fact_knows. eauto using all_done_with_cons_done. }
      assert (Hmhyps : Forall (fun q => program.interp p (op_knows_fact inputs)
                                          (fact.meta (known_meta_fact known q))) pats).
      { eapply Forall_impl; [exact Hdone_pats|]. eauto using known_meta_fact_knows. }
      eapply pftree.step with (l := map fact.meta (map (known_meta_fact known) pats)).
      2:{ rewrite !Lists.List.Forall_map. exact Hmhyps. }
      constructor. apply Exists_exists. exists mr. split; [exact Hmr|].
      assert (Hpats : map meta_fact.pattern (map (known_meta_fact known) pats) = pats).
      { rewrite map_map. erewrite map_ext; [apply map_id|]. reflexivity. }
      split; [rewrite Hpats; exact Hpi|].
      intros nf Hm.
      rewrite (program.one_step_derives_iff p (op_knows_fact inputs) mr
                 (map (known_meta_fact known) pats) mf.(meta_fact.pattern) nf); try assumption.
      + cbv [meta_fact.consistent_with] in Hcons. rewrite Hcons by assumption. split.
        * intros (src & [Heq | Hin]); [discriminate|].
          apply (Hcorrect (fact.normal nf)). exists src. exact Hin.
        * intros Himpl.
          eapply derivable_matches_known; eauto using sane_meta_facts_correct, sane_meta_facts_ok.
          apply incl_tl. apply Hsane.
      + apply good_input_set_inputs. assumption.
      + rewrite Hpats. exact Hpi.
      + rewrite Lists.List.Forall_map. eapply Forall_impl; [exact Hmhyps|].
        eauto using derived_meta_fact_honest.
      + intros mh mf' Hmh Himpl' Hpe. apply in_map_iff in Hmh. fwd.
        apply meta_fact.eq_of_agree; [assumption|].
        rewrite Forall_forall in Hmhyps. eauto using derived_meta_facts_agree.
      + rewrite Lists.List.Forall_map. exact Hmhyps.
  Qed.

  Lemma comp_steps_sound inputs known known' :
    good_input_facts inputs ->
    sane_state inputs known ->
    state_correct inputs known ->
    comp_step^* known known' ->
    state_correct inputs known'.
  Proof.
    intros Hinp Hsane Hcorrect Hsteps. revert Hsane Hcorrect.
    induction Hsteps; eauto using step_preserves_sane, comp_step_sound.
  Qed.

  Lemma steps_preserves_has_derived known known' f :
    comp_step^* known known' ->
    has_derived_datalog_fact known f -> has_derived_datalog_fact known' f.
  Proof.
    intros Hsteps. pose proof (comp_steps_incl _ _ Hsteps) as Hincl.
    destruct f; cbv [has_derived_datalog_fact];
      eauto using all_done_with_incl, op_knows_normal_fact_incl.
  Qed.

  Lemma compose_completion inputs known hyps :
    good_input_facts inputs ->
    sane_state inputs known ->
    state_correct inputs known ->
    Forall (fun h =>
      forall known0,
        sane_state inputs known0 ->
        state_correct inputs known0 ->
        exists known', comp_step^* known0 known' /\ has_derived_datalog_fact known' h) hyps ->
    exists known',
      comp_step^* known known' /\
      Forall (has_derived_datalog_fact known') hyps.
  Proof.
    intros Hinp Hsane Hcorrect HF. revert known Hsane Hcorrect.
    induction HF as [|h hs Hh Hhs IH]; intros known Hsane Hcorrect.
    - exists known. split; [apply rt1n_refl|]. constructor.
    - destruct (IH known Hsane Hcorrect) as (known_mid & Hsteps_mid & Hderived_hs).
      destruct (Hh known_mid) as (known' & Hsteps' & Hh_derived);
        eauto using steps_preserves_sane, comp_steps_sound.
      exists known'. split; [eauto using crt1n_trans_compose|].
      constructor; [exact Hh_derived|].
      eapply Forall_impl; [exact Hderived_hs|]. eauto using steps_preserves_has_derived.
  Qed.

  Lemma knows_fact_inputs_has_derived inputs known f :
    incl inputs known ->
    op_knows_fact inputs f ->
    has_derived_datalog_fact known f.
  Proof.
    intros Hincl.
    destruct f as [nf | mf]; cbv [op_knows_fact op_knows_meta_fact has_derived_datalog_fact].
    - eauto using op_knows_normal_fact_incl.
    - intros (Hdone & _). eauto using all_done_with_incl.
  Qed.

  Lemma comp_step_fire_normal known rn nf :
    In rn p.(program.rules) ->
    op_can_deduce_normal_fact rn known nf ->
    comp_step known (op_message.normal nf (op_source.rule rn) :: known).
  Proof.
    intros Hrn Hcdn. exists (op_message.normal nf (op_source.rule rn)), rn.
    cbv [can_deduce_message]. auto.
  Qed.

  Lemma comp_step_fire_meta known rn pat :
    In rn p.(program.rules) ->
    ok_to_deduce rn known pat ->
    op_can_deduce_pattern known pat ->
    comp_step known (op_message.done_with pat (op_source.rule rn) :: known).
  Proof.
    intros Hrn Hok Hcdp. exists (op_message.done_with pat (op_source.rule rn)), rn.
    cbv [can_deduce_message]. auto.
  Qed.

  (* Drive rule [rn] to derive every fact matching [mf]'s pattern that it can,
     so that its done message becomes [ok_to_deduce]. Termination: every such
     fact is in the (real, finite) meta fact's set. *)
  Lemma rule_can_force_normal_facts inputs known rn (mf : meta_fact) :
    good_input_facts inputs ->
    sane_state inputs known ->
    state_correct inputs known ->
    In rn p.(program.rules) ->
    program.interp p (op_knows_fact inputs) (fact.meta mf) ->
    exists known',
      comp_step^* known known' /\
        ok_to_deduce rn known' mf.(meta_fact.pattern).
  Proof.
    intros Hinp Hsane Hcorrect Hrn Hpi_meta.
    pose proof (derived_meta_fact_honest _ _ Hinp Hpi_meta) as Hhonest.
    cbv [meta_fact.consistent_with fact.normal_subset] in Hhonest.
    set (l := map (fun a => {| normal_fact.rel := mf.(meta_fact.pattern).(fact_pattern.rel);
                          normal_fact.args := a |}) (map.keys mf.(meta_fact.set))).
    assert (Hcand : forall nf known',
               comp_step^* known known' ->
               In (op_message.normal nf (op_source.rule rn)) known' ->
               fact_pattern.matches mf.(meta_fact.pattern) nf ->
               In (op_message.normal nf (op_source.rule rn)) known \/ In nf l).
    { intros nf known' Hsteps Hin Hm. right.
      pose proof (comp_steps_sound _ _ _ Hinp Hsane Hcorrect Hsteps (fact.normal nf)
                    (ex_intro _ (op_source.rule rn) Hin)) as Himpl.
      apply Hhonest in Himpl; [|assumption].
      destruct nf as [nrel nargs]. destruct Hm as (Hrel & _). cbn in Hrel, Himpl.
      subst l. apply in_map_iff. exists nargs. split; [f_equal; congruence | exact Himpl]. }
    clearbody l. clear Hhonest Hpi_meta.
    remember (length l) as len eqn:Elen. assert (Hlen : length l <= len) by lia. clear Elen.
    revert l known Hlen Hsane Hcorrect Hcand.
    induction len as [|len IH]; intros l known Hlen Hsane Hcorrect Hcand.
    - exists known. split; [apply rt1n_refl|]. intros nf Hcdn Hm.
      destruct l; [|simpl in Hlen; lia].
      pose proof (comp_step_fire_normal _ _ _ Hrn Hcdn) as Hstep.
      destruct (Hcand nf (op_message.normal nf (op_source.rule rn) :: known)
                  (Relation_Operators.rt1n_trans _ _ _ _ _ Hstep (rt1n_refl _ _ _))
                  (or_introl eq_refl) Hm) as [Hin | []]. exact Hin.
    - destruct (classic (Exists (fun nf =>
                            op_can_deduce_normal_fact rn known nf /\
                            fact_pattern.matches mf.(meta_fact.pattern) nf /\
                            ~ In (op_message.normal nf (op_source.rule rn)) known) l))
        as [Hex | Hno].
      + apply Exists_exists in Hex. destruct Hex as (nf & Hin_l & Hcdn & Hm & Hnin).
        apply in_split in Hin_l. destruct Hin_l as (l1 & l2 & ->).
        pose proof (comp_step_fire_normal _ _ _ Hrn Hcdn) as Hstep.
        destruct (IH (l1 ++ l2) (op_message.normal nf (op_source.rule rn) :: known))
          as (known' & Hsteps' & Hok).
        * rewrite length_app in *. simpl in *. lia.
        * eauto using step_preserves_sane.
        * eauto using comp_step_sound.
        * intros nf0 known'' Hsteps'' Hin'' Hm''.
          destruct (Hcand nf0 known''
                      (Relation_Operators.rt1n_trans _ _ _ _ _ Hstep Hsteps'') Hin'' Hm'')
            as [Hc | Hc].
          -- left. right. exact Hc.
          -- apply in_app_iff in Hc. destruct Hc as [Hc | [Hc | Hc]].
             ++ right. apply in_or_app. left. exact Hc.
             ++ subst. left. left. reflexivity.
             ++ right. apply in_or_app. right. exact Hc.
        * exists known'. split; [eauto | exact Hok].
      + exists known. split; [apply rt1n_refl|]. intros nf Hcdn Hm.
        destruct (classic (In (op_message.normal nf (op_source.rule rn)) known))
          as [Hin | Hnin]; [exact Hin | exfalso].
        pose proof (comp_step_fire_normal _ _ _ Hrn Hcdn) as Hstep.
        destruct (Hcand nf (op_message.normal nf (op_source.rule rn) :: known)
                    (Relation_Operators.rt1n_trans _ _ _ _ _ Hstep (rt1n_refl _ _ _))
                    (or_introl eq_refl) Hm) as [Hc | Hc]; [contradiction|].
        apply Hno. apply Exists_exists. eauto 6.
  Qed.

  Lemma all_rules_done inputs known (mf : meta_fact) :
    good_input_facts inputs ->
    sane_state inputs known ->
    state_correct inputs known ->
    op_can_deduce_pattern known mf.(meta_fact.pattern) ->
    program.interp p (op_knows_fact inputs) (fact.meta mf) ->
    exists known',
      comp_step^* known known' /\
        all_done_with known' mf.(meta_fact.pattern).
  Proof.
    intros Hinp Hsane Hcorrect Hcdp Hpi_meta.
    enough (Hgoal : forall rs, incl rs p.(program.rules) ->
              exists known', comp_step^* known known' /\
                Forall (fun r => In (op_message.done_with mf.(meta_fact.pattern) (op_source.rule r)) known') rs).
    { destruct (Hgoal _ (incl_refl _)) as (known' & Hsteps & Hall).
      exists known'. split; [exact Hsteps|].
      cbv [all_done_with]. rewrite (can_deduce_pattern_not_input _ _ Hcdp). exact Hall. }
    induction rs as [|r0 rs IH]; intros Hincl.
    - exists known. split; [apply rt1n_refl | constructor].
    - destruct IH as (known1 & Hsteps1 & Hdone_rs); [eauto using incl_tran, incl_tl, incl_refl|].
      assert (Hr0 : In r0 p.(program.rules)) by (apply Hincl; left; reflexivity).
      destruct (rule_can_force_normal_facts inputs known1 r0 mf)
        as (known2 & Hsteps2 & Hok); eauto using steps_preserves_sane, comp_steps_sound.
      assert (Hcdp2 : op_can_deduce_pattern known2 mf.(meta_fact.pattern)).
      { eapply op_can_deduce_pattern_incl; [|exact Hcdp].
        apply comp_steps_incl. eauto using crt1n_trans_compose. }
      pose proof (comp_step_fire_meta known2 r0 _ Hr0 Hok Hcdp2) as Hstep.
      eexists. split.
      { eapply crt1n_trans_compose; [exact Hsteps1|]. eapply crt1n_trans_compose; [exact Hsteps2|].
        eapply Relation_Operators.rt1n_trans; [exact Hstep | apply rt1n_refl]. }
      constructor; [left; reflexivity|].
      eapply Forall_impl; [exact Hdone_rs|]. intros r1 Hr1. right.
      apply (comp_steps_incl _ _ Hsteps2). exact Hr1.
  Qed.

  Lemma good_layout_complete_rule inputs known f hyps :
    good_input_facts inputs ->
    sane_state inputs known ->
    state_correct inputs known ->
    program.interp_step p f hyps ->
    Forall (op_knows_fact known) hyps ->
    exists known',
      comp_step^* known known' /\
        has_derived_datalog_fact known' f.
  Proof.
    intros Hinp Hsane Hcorrect Himpl Hknown. invert Himpl.
    - apply Exists_exists in H. destruct H as (rn & Hrn & Hri).
      exists (op_message.normal f0 (op_source.rule rn) :: known).
      split; [| eexists; left; reflexivity].
      eapply Relation_Operators.rt1n_trans; [|apply rt1n_refl].
      apply (comp_step_fire_normal _ rn); [assumption|]. exists hyps. auto.
    - apply Exists_exists in H. destruct H as (mr & Hmr & Hmri).
      cbv [has_derived_datalog_fact]. apply (all_rules_done inputs known f0); try assumption.
      + exists mr, (map meta_fact.pattern hyps0). ssplit; [assumption | apply Hmri |].
        rewrite Lists.List.Forall_map in Hknown |- *.
        eapply Forall_impl; [exact Hknown|]. intros mh (Hdone & _). exact Hdone.
      + eapply pftree.step.
        * constructor. apply Exists_exists. eauto.
        * eapply Forall_impl; [exact Hknown|]. auto.
  Qed.

  Definition state_complete (inputs known : list op_message) :=
    forall f,
      program.interp p (op_knows_fact inputs) f ->
      exists known',
        comp_step^* known known' /\
          has_derived_datalog_fact known' f.

  Lemma comp_step_complete inputs known :
    good_input_facts inputs ->
    sane_state inputs known ->
    state_correct inputs known ->
    state_complete inputs known.
  Proof.
    intros Hinp Hsane Hcorrect f Himpl.
    set (R := fun f0 =>
                forall known0,
                  sane_state inputs known0 ->
                  state_correct inputs known0 ->
                  exists known', comp_step^* known0 known' /\ has_derived_datalog_fact known' f0).
    enough (HR : R f) by (apply HR; assumption).
    revert f Himpl. apply pftree.ind.
    - intros f0 Hkdf known0 Hsane0 Hcorrect0.
      exists known0. split; [apply rt1n_refl|].
      eapply knows_fact_inputs_has_derived; [apply Hsane0 | exact Hkdf].
    - intros f0 hyps Hstep0 Hforall_pi Hforall_R known0 Hsane0 Hcorrect0.
      destruct (compose_completion inputs known0 hyps Hinp Hsane0 Hcorrect0 Hforall_R)
        as (known1 & Hsteps1 & Hderived1).
      assert (Hsane1 : sane_state inputs known1) by eauto using steps_preserves_sane.
      assert (Hcorrect1 : state_correct inputs known1) by eauto using comp_steps_sound.
      destruct (good_layout_complete_rule inputs known1 f0 hyps)
        as (known2 & Hsteps2 & Hderived2); try assumption.
      { eapply Forall_impl; [apply Forall_and; [exact Hforall_pi | exact Hderived1]|].
        simpl. intros h (Hpi_h & Hd_h). apply op_knows_fact_iff.
        eauto using correct_impl_consistent. }
      exists known2. split; [eauto using crt1n_trans_compose | exact Hderived2].
  Qed.

  Lemma good_input_no_rule_done inputs pat r :
    good_input_facts inputs -> ~ In (op_message.done_with pat (op_source.rule r)) inputs.
  Proof.
    intros Hinp Hin. cbv [good_input_facts] in Hinp. rewrite Forall_forall in Hinp.
    apply Hinp in Hin. discriminate.
  Qed.

  Lemma sane_initial inputs :
    good_input_facts inputs -> sane_state inputs inputs.
  Proof.
    intros Hinp. constructor.
    - apply incl_refl.
    - apply Forall_forall. intros r _ pat Hin. exfalso. eapply good_input_no_rule_done; eassumption.
    - apply Forall_forall. intros r _ pat Hin. exfalso. eapply good_input_no_rule_done; eassumption.
  Qed.

  Lemma sc_initial inputs : state_correct inputs inputs.
  Proof. intros f Hf. apply pftree.leaf. exact Hf. Qed.

  Theorem prog_impl_iff_comp_step inputs f :
    good_input_facts inputs ->
    (program.interp p (op_knows_fact inputs) f <->
     exists known, comp_step^* inputs known /\
                   has_derived_datalog_fact known f /\ mf_consistent_state known f).
  Proof.
    intros Hinp.
    pose proof (sane_initial _ Hinp) as Hsane. pose proof (sc_initial inputs) as Hsc.
    split.
    - intros Hprog.
      destruct (comp_step_complete _ _ Hinp Hsane Hsc _ Hprog) as (known & Hsteps & Hderiv).
      exists known. ssplit; [exact Hsteps | exact Hderiv |].
      eapply correct_impl_consistent; eauto using comp_steps_sound.
    - intros (known & Hsteps & Hderiv & Hcons).
      eapply comp_steps_sound; eauto. apply op_knows_fact_iff. auto.
  Qed.

End __.

Arguments sane_state
  {_rel _exprvar _fn _aggregator _value semantics context value_eqb value_eqb_ok value_set value_set_ok}
  is_input p input_facts known.
