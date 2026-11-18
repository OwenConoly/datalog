From Stdlib Require Import List Lia Permutation RelationClasses.
From Datalog Require Import List Datalog Smallstep Tactics Graph Decidable.
From coqutil Require Import Map.Interface Eqb.
From coqutil Require Import Semantics.OmniSmallstepCombinators Tactics Tactics.fwd.
Import ListNotations.

Definition sender_labelT := Type.
Existing Class sender_labelT.
#[global] Typeclasses Transparent sender_labelT.

(*a specification for how a datalog node should behave.
  eventually, an "implementation" should live in Local.v.
  i expect we'll want to do "Import node" in files that don't think about the implementation.
  this module wraps almost the whole file, so let's not indent inside of it.
 *)
Module node.
Module action_label.
  Section __.
    Context `{params : datalog_params}.

    Variant action_label :=
      | normal (nf : normal_fact)
      | done_with (pattern : fact_pattern).
  End __.
End action_label. Abbreviation action_label := action_label.action_label.

Module message.
  Section __.
    Context `{params : datalog_params} {sender_label : sender_labelT}.
    Context (R_senders : rel -> list sender_label).

    Variant message :=
    | normal (nf : normal_fact)
    | done_with (pattern : fact_pattern) (src : sender_label) (count : nat).

    Definition is_normal (f : message) : bool :=
      match f with
      | normal _ => true
      | done_with _ _ _ => false
      end.

    Definition as_normal (f : message) : option normal_fact :=
      match f with
      | normal nf => Some nf
      | done_with _ _ _ => None
      end.

    Lemma in_filter_map_as_normal nf l :
      In nf (filter_map as_normal l) <-> In (normal nf) l.
    Proof.
      rewrite in_filter_map. split.
      - intros ([nf' | ] & Hin & Hnf); simpl in Hnf; congruence.
      - intros Hin. eexists. split; [exact Hin|]. reflexivity.
    Qed.

    Definition rel (f : message) : rel :=
      match f with
      | normal nf => nf.(normal_fact.rel)
      | done_with pat _ _ => pat.(fact_pattern.rel)
      end.

    Definition matches (pat : fact_pattern) (f : message) :=
      match f with
      | normal nf => fact_pattern.matches pat nf
      | done_with _ _ _ => False
      end.

    Definition matchesb (pat : fact_pattern) (f : message) :=
      match f with
      | normal nf => fact_pattern.matchesb pat nf
      | done_with _ _ _ => false
      end.

    #[global] Instance matchesb_spec pat f :
      Reflects (matches pat f) (matchesb pat f).
    Proof. destruct f; cbn [matches matchesb]; [exact _ | constructor; auto]. Qed.

    Lemma Existsn_matches_filter_map_as_normal pat n l :
      Existsn (matches pat) n l <-> Existsn (fact_pattern.matches pat) n (filter_map as_normal l).
    Proof.
      apply Existsn_filter_map. intros [nf | ]; simpl; split; intros; fwd; (eauto || contradiction || discriminate).
    Qed.

    Definition equiv (f1 f2 : message) :=
      match f1, f2 with
      | done_with p1 s1 _, done_with p2 s2 _ => p1 = p2 /\ s1 = s2
      | _, _ => f1 = f2
      end.

    Definition label (f : message) :=
      match f with
      | normal nf => action_label.normal nf
      | done_with pat _ _ => action_label.done_with pat
      end.

    Lemma equiv_Equivalence : Equivalence equiv.
    Proof.
      constructor.
      - intros f. destruct f; simpl; auto.
      - intros f1 f2. destruct f1, f2; simpl; intros; fwd; auto || congruence.
      - intros f1 f2 f3. destruct f1, f2, f3; simpl; intros; fwd; auto || congruence.
    Qed.
  End __.
End message. Abbreviation message := message.message.

(*hmm this is the same thing as action_label, but conceptually they are different...*)
Module claim.
  Section __.
    Context `{params : datalog_params} {sender_label : sender_labelT}.

    Variant claim :=
      | normal (nf : normal_fact)
      | done_with (pattern : fact_pattern) (tuples : list value -> Prop).

    Definition interp (name : sender_label) (P : claim) (ms : list message) :=
      match P with
      | normal nf => In (message.normal nf) ms
      | done_with pat tuples =>
          exists num,
          In (message.done_with pat name num) ms /\
            Existsn_ge (message.matches pat) num ms /\
            forall nf,
              fact_pattern.matches pat nf ->
              In (message.normal nf) ms <-> tuples nf.(normal_fact.args)
      end.

    Lemma interp_mono name P : multiset_monotone_inc (interp name P).
    Proof.
      intros ms1 ms2 H Hsub. destruct P; cbv [interp] in *.
      - eapply submultiset_incl; eassumption.
      - fwd. eexists. split.
        + eapply submultiset_incl; eassumption.
        + eapply Existsn_ge_submultiset; eassumption.
    Qed.

    Definition interp_conj (name : sender_label) (Ps : list claim) (ms : list message) :=
      Forall (fun P => interp name P ms) Ps.

    Lemma interp_conj_mono name Ps : multiset_monotone_inc (interp_conj name Ps).
    Proof.
      intros ms1 ms2 H Hsub. eapply Forall_impl; [ exact H | ].
      intros. cbv beta in *. eapply interp_mono; eassumption.
    Qed.
  End __.
End claim. Abbreviation claim := claim.claim.

Module state.
  Section __.
    Context `{params : datalog_params} {sender_label : sender_labelT}.

    Record state := mk
      { known : list message;
        sent : list message }.

    Definition add_to_known inps s :=
      {| known := inps ++ s.(known);
        sent := s.(sent) |}.
  End __.
End state. Abbreviation state := state.state.

Section __.
  Context `{params : datalog_params} {sender_label : sender_labelT}.
  Context (R_senders : rel -> list sender_label).

  Definition knows_normal_fact (known : list message) (nf : normal_fact) :=
    In (message.normal nf) known.

  Definition expects_num_facts (senders : list sender_label) (pat : fact_pattern) (known : list message) num :=
    exists expected_msgss,
      Forall2 (fun n expected_msgs => In (message.done_with pat n expected_msgs) known)
        senders expected_msgss /\
        num = list_sum expected_msgss.

  Definition knows_meta_fact (known : list message) (mf : meta_fact) :=
    exists num,
      expects_num_facts (R_senders (meta_fact.rel mf)) mf.(meta_fact.pattern) known num /\
        Existsn (message.matches mf.(meta_fact.pattern)) num known /\
        meta_fact.consistent_with mf (knows_normal_fact known).

  Definition knows_fact dfacts f :=
    match f with
    | fact.normal nf => knows_normal_fact dfacts nf
    | fact.meta mf => knows_meta_fact dfacts mf
    end.

  Definition can_deduce_normal_fact (r : rule) (known : list message) (nf : normal_fact) :=
    exists hyps,
      rule.interp r nf hyps /\
        Forall (knows_fact known) hyps.

  Definition can_deduce_pattern (mr : meta_rule) (known : list message) (pat : fact_pattern) :=
    exists mhyps,
      meta_rule.pattern_interp mr pat (map meta_fact.pattern mhyps) /\
        Forall (knows_meta_fact known) mhyps.

  Context (p : program) (name : sender_label).

  Definition counted (sent : list message) (nf : normal_fact) :=
    exists pat num,
      In (message.done_with pat name num) sent /\ fact_pattern.matches pat nf.

  Definition saturated (ns : state) (pat : fact_pattern) :=
    forall r nf,
      In r p.(program.rules) ->
      can_deduce_normal_fact r ns.(state.known) nf ->
      fact_pattern.matches pat nf ->
      In (message.normal nf) ns.(state.sent).

  Definition can_deduce (ns : state) (m : message) :=
    match m with
    | message.normal nf =>
        Exists (fun r => can_deduce_normal_fact r ns.(state.known) nf) p.(program.rules) /\
          ~ counted ns.(state.sent) nf
    | message.done_with pat src num =>
        src = name /\
          Exists (fun mr => can_deduce_pattern mr ns.(state.known) pat) p.(program.meta_rules) /\
          Existsn (message.matches pat) num ns.(state.sent) /\
          saturated ns pat
    end.

  Definition can_claim (inps : list message) (c : claim) :=
    match c with
    | claim.normal nf =>
        exists hyps,
        program.interp_step p (fact.normal nf) hyps /\
          Forall (knows_fact inps) hyps
    | claim.done_with pat =>
        exists mf hyps,
        mf.(meta_fact.pattern) = pat /\
          program.interp_step p (fact.meta mf) hyps /\
          Forall (knows_fact inps) hyps
    end.

  Definition can_claim_conj (inps : list message) := Forall (can_claim inps).

  Local Abbreviation IO_event := (Smallstep.IO_event action_label message).

  Inductive step : state -> IO_event -> state -> Prop :=
  | deduce_step ns output :
    can_deduce ns output ->
    step ns (O_event (message.label output) [output])
      {| state.known := ns.(state.known);
        state.sent := output :: ns.(state.sent) |}
  | input_step rs input :
    step rs (I_event input)
      {| state.known := input :: rs.(state.known);
        state.sent := rs.(state.sent) |}.

  Definition safe_inputs (inputs : list message) :=
    forall pat expected_msgss,
      Forall2 (fun k e => In (message.done_with pat k e) inputs)
              (R_senders pat.(fact_pattern.rel)) expected_msgss ->
      Existsn_le (message.matches pat) (list_sum expected_msgss) inputs.

  Definition init : state :=
    {| state.known := []; state.sent := [] |}.

  Definition safe_output (fs : list message) :=
    (forall pat src cnt,
        In (message.done_with pat src cnt) fs ->
        name = src /\ Existsn_le (message.matches pat) cnt fs) /\
      (forall nf, In (message.normal nf) fs -> In name (R_senders nf.(normal_fact.rel))).

  Lemma safe_output_mono : multiset_monotone_dec safe_output.
  Proof.
    cbv [multiset_monotone_dec safe_output]. intros ? ? H1 H2. fwd.
    split; eauto using submultiset_incl, incl_def.
    intros. especialize H1p0; eauto using submultiset_incl, incl_def. fwd. eauto using Existsn_le_submultiset.
  Qed.

  Lemma submultiset_rest_no_matches pat small rest big num :
    Permutation big (small ++ rest) ->
    safe_inputs big ->
    expects_num_facts (R_senders pat.(fact_pattern.rel)) pat small num ->
    Existsn (message.matches pat) num small ->
    Forall (fun x => ~ message.matches pat x) rest.
  Proof.
    intros Hperm Hallow Hexp Hex.
    pose proof (submultiset_incl _ _ (ex_intro _ rest Hperm)) as Hincl.
    destruct Hexp as (ems & Hf2 & Hsum).
    assert (Hf2' : Forall2 (fun k e => In (message.done_with pat k e) big)
                           (R_senders pat.(fact_pattern.rel)) ems)
      by (clear -Hf2 Hincl; induction Hf2; constructor;
            [apply Hincl; assumption | assumption]).
    pose proof (Existsn_le_perm _ _ _ _ Hperm (Hallow pat ems Hf2')) as Hle.
    apply Forall_forall. intros x Hx Hmatch.
    pose proof (Existsn_ge_of_Existsn _ _ _ Hex num (le_n num)) as Hge_small.
    pose proof (Existsn_ge_app _ _ _ _ _ Hge_small (Existsn_ge_1 _ _ _ Hx Hmatch)) as Hge_app.
    pose proof (Existsn_ge_le_bound _ _ _ _ Hge_app Hle). lia.
  Qed.

  Lemma knows_fact_submultiset l1 l2 h :
    submultiset l1 l2 -> safe_inputs l2 ->
    knows_fact l1 h -> knows_fact l2 h.
  Proof.
    intros Hsub Hallow Hk. pose proof (submultiset_incl _ _ Hsub) as Hincl.
    destruct Hsub as (rest & Hperm).
    destruct h as [nf | mf].
    - apply Hincl. exact Hk.
    - destruct Hk as (num & Hexp & Hexn & Hiff).
      pose proof (submultiset_rest_no_matches mf.(meta_fact.pattern) l1 rest l2 num
                    Hperm Hallow Hexp Hexn) as Hrest_no.
      exists num. split; [| split].
      + destruct Hexp as (ems & Hf2 & Hsum). exists ems. split; [| exact Hsum].
        clear -Hf2 Hincl. induction Hf2; constructor; [apply Hincl; assumption | assumption].
      + eapply Existsn_perm; [ | apply Permutation_sym; exact Hperm ].
        replace num with (num + 0) by lia.
        apply Existsn_app; [ exact Hexn | apply Forall_not_Existsn_0; exact Hrest_no ].
      + intros nf Hm. specialize (Hiff nf Hm). split; intro H.
        * apply Hincl. apply (proj1 Hiff). exact H.
        * apply (proj2 Hiff).
          pose proof (Permutation_in _ Hperm H) as H'.
          apply in_app_or in H'. destruct H' as [Hin1 | Hinr]; [exact Hin1 |].
          exfalso. rewrite Forall_forall in Hrest_no.
          apply (Hrest_no _ Hinr). exact Hm.
  Qed.

  Lemma sent_eq_outputs t s :
    star step init t s -> s.(state.sent) = flat_map outputs_of t.
  Proof.
    induction 1; [ reflexivity | ].
    invert H0; cbn; congruence.
  Qed.

  Lemma sent_source_correct t s pat src num :
    star step init t s ->
    In (message.done_with pat src num) s.(state.sent) ->
    src = name.
  Proof.
    induction 1; [ destruct 1 | ].
    intros Hin. invert H0; cbn [state.sent] in Hin; [ | auto ].
    destruct Hin as [-> | Hin]; [ | auto ].
    cbn [can_deduce] in *. fwd. congruence.
  Qed.

  Lemma sent_counts_correct t s pat num :
    star step init t s ->
    In (message.done_with pat name num) s.(state.sent) ->
    Existsn (message.matches pat) num s.(state.sent).
  Proof.
    induction 1; [ destruct 1 | ].
    intros Hin. invert H0; cbn [state.sent] in *; [ | auto ].
    destruct Hin as [-> | Hin].
    - cbn [can_deduce] in *. fwd. apply Existsn_no; [ intros [] | assumption ].
    - apply Existsn_no; [ | auto ].
      intros Hmatch. destruct output as [nf' | pat' src' cnt']; [ | exact Hmatch ].
      cbn [can_deduce] in *. cbv [counted] in *. fwd. eauto.
  Qed.

  Lemma can_deduce_normal_concl_rel ns nf :
    can_deduce ns (message.normal nf) -> In nf.(normal_fact.rel) (program.normal_concl_rels p).
  Proof.
    cbn [can_deduce]. intros (Hex & _). apply Exists_exists in Hex.
    destruct Hex as (r & Hr & hyps & Hri & _).
    eapply program.rule_normal_concl_rel_in; eauto using rule.interp_concl_relname_in.
  Qed.

  Lemma safe_inputs_submultiset l1 l2 :
    submultiset l1 l2 -> safe_inputs l2 -> safe_inputs l1.
  Proof.
    intros Hsub Hbound pat ems Hf2.
    pose proof (submultiset_incl _ _ Hsub) as Hincl.
    assert (Hf2' : Forall2 (fun k e => In (message.done_with pat k e) l2)
                           (R_senders pat.(fact_pattern.rel)) ems)
      by (clear -Hf2 Hincl; induction Hf2; constructor;
            [apply Hincl; assumption | assumption]).
    eapply Existsn_le_submultiset; [ apply Hbound; exact Hf2' | exact Hsub ].
  Qed.

  Lemma knows_fact_transfer_down_sub small big mhyps h :
    submultiset small big ->
    safe_inputs big ->
    Forall (knows_meta_fact small) mhyps ->
    fact.covered_by_pats (map meta_fact.pattern mhyps) h ->
    knows_fact big h ->
    knows_fact small h.
  Proof.
    intros Hsub Hallow Hhyps Hcov Hknow_big.
    pose proof (submultiset_incl _ _ Hsub) as Hincl.
    destruct Hsub as (rest & Hperm).
    cbv [fact.covered_by_pats] in Hcov. apply Exists_exists in Hcov.
    destruct Hcov as (fp & Hfp & Hcov). apply in_map_iff in Hfp.
    destruct Hfp as (mh & Hfp & Hmh). subst fp.
    rewrite Forall_forall in Hhyps. specialize (Hhyps _ Hmh).
    destruct Hhyps as (num_h & Hexp_h & Hex_h & _).
    pose proof (submultiset_rest_no_matches mh.(meta_fact.pattern) small rest big num_h
                  Hperm Hallow Hexp_h Hex_h) as Hrest_no.
    rewrite Forall_forall in Hrest_no.
    destruct h as [nf | mf]; simpl in Hcov.
    - cbn [knows_fact knows_normal_fact] in Hknow_big |- *.
      pose proof (Permutation_in _ Hperm Hknow_big) as Hin_app.
      apply in_app_or in Hin_app. destruct Hin_app as [Hin | Hinr]; [exact Hin |].
      exfalso. apply (Hrest_no _ Hinr). exact Hcov.
    - destruct Hknow_big as (num_new & Hexp_new & Hex_new & Hiff_new).
      cbv [meta_fact.rel] in Hexp_h. rewrite Hcov in Hexp_h, Hex_h, Hrest_no.
      exists num_h. split; [exact Hexp_h | split; [exact Hex_h |]].
      intros nf Hm. specialize (Hiff_new nf Hm). split.
      + intro Hset. apply Hiff_new in Hset.
        pose proof (Permutation_in _ Hperm Hset) as Hin_app.
        apply in_app_or in Hin_app. destruct Hin_app as [Hin | Hinr]; [exact Hin |].
        exfalso. apply (Hrest_no _ Hinr). exact Hm.
      + intro Hin. apply Hiff_new. apply Hincl. exact Hin.
  Qed.

  (*every done-message this node has sent could still be deduced now*)
  Definition sent_dones_ok (s : state) : Prop :=
    forall pat num,
      In (message.done_with pat name num) s.(state.sent) ->
      can_deduce s (message.done_with pat name num).

  Definition good (s : state) (t : list IO_event) :=
    s.(state.known) = flat_map inputs_of t /\
    safe_inputs (flat_map inputs_of t) /\
    sent_dones_ok s.

  Lemma good_init : good init [].
  Proof.
    split; [reflexivity | split].
    - intros pat ems _. apply El_nil.
    - intros pat num H. destruct H.
  Qed.

  Lemma step_star_mono s t' s' :
    star step s t' s' ->
    submultiset s.(state.known) s'.(state.known) /\
    submultiset s.(state.sent) s'.(state.sent).
  Proof.
    intros Hstar. induction Hstar as [| t0 sa e sb Hstar' IH Hstep].
    - split; apply submultiset_refl.
    - destruct IH as (IHk & IHs).
      assert (submultiset sa.(state.known) sb.(state.known) /\
              submultiset sa.(state.sent) sb.(state.sent)) as (Hk & Hs).
      { invert Hstep; cbn [state.known state.sent];
          split; try apply submultiset_refl; apply submultiset_cons. }
      split; eapply submultiset_trans; eassumption.
  Qed.

  Lemma known_eq_inputs t s :
    star step init t s -> s.(state.known) = flat_map inputs_of t.
  Proof.
    intros Hstar. induction Hstar as [| T0 sm e s Hstar_T IH Hstep].
    - reflexivity.
    - invert Hstep; cbn [state.known inputs_of flat_map app];
        rewrite IH; reflexivity.
  Qed.

  Lemma known_input_free s t s' :
    star step s t s' -> flat_map inputs_of t = [] -> s'.(state.known) = s.(state.known).
  Proof.
    intros Hstar. induction Hstar as [| t0 sa e sb Hstar IH Hstep]; intros Hinp.
    - reflexivity.
    - invert Hstep; cbn [inputs_of flat_map app] in Hinp.
      + exact (IH Hinp).
      + discriminate Hinp.
  Qed.

  Definition knows_incl (l1 l2 : list message) : Prop :=
    forall f, knows_fact l1 f -> knows_fact l2 f.

  Lemma knows_incl_grow l1 l2 l2' :
    knows_incl l1 l2 -> submultiset l2 l2' -> safe_inputs l2' -> knows_incl l1 l2'.
  Proof.
    intros Hki Hsub Hallow f Hf.
    eapply knows_fact_submultiset; [ exact Hsub | exact Hallow | apply Hki; exact Hf ].
  Qed.

  Lemma knows_fact_transfer_down small big mhyps h :
    knows_incl small big ->
    Forall (knows_meta_fact small) mhyps ->
    fact.covered_by_pats (map meta_fact.pattern mhyps) h ->
    knows_fact big h ->
    knows_fact small h.
  Proof.
    intros Hki Hhyps Hcov Hknow_big.
    cbv [fact.covered_by_pats] in Hcov. apply Exists_exists in Hcov.
    destruct Hcov as (fp & Hfp & Hcov). apply in_map_iff in Hfp.
    destruct Hfp as (mh & Hfp & Hmh). subst fp.
    rewrite Forall_forall in Hhyps. specialize (Hhyps _ Hmh).
    pose proof (Hki (fact.meta mh) Hhyps) as Hkb.
    destruct h as [nf | mf]; simpl in Hcov.
    - destruct Hhyps as (_ & _ & _ & Hiff_s). destruct Hkb as (_ & _ & _ & Hiff_b).
      apply (proj1 (Hiff_s nf Hcov)). apply (proj2 (Hiff_b nf Hcov)). exact Hknow_big.
    - destruct Hhyps as (num_s & Hexp_s & Hex_s & Hiff_s).
      destruct Hknow_big as (_ & _ & _ & Hiff_b). destruct Hkb as (_ & _ & _ & Hiff_b').
      cbv [meta_fact.rel] in Hexp_s. rewrite Hcov in Hexp_s, Hex_s.
      exists num_s. split; [ exact Hexp_s | split; [ exact Hex_s | ] ].
      intros nf Hm.
      assert (Hm' : fact_pattern.matches mh.(meta_fact.pattern) nf)
        by (rewrite Hcov; exact Hm).
      specialize (Hiff_s nf Hm'). specialize (Hiff_b nf Hm). specialize (Hiff_b' nf Hm').
      cbv [knows_normal_fact] in *. tauto.
  Qed.

  Definition nle (s1 s2 : state) :=
    knows_incl s1.(state.known) s2.(state.known) /\
      incl_mod message.equiv s1.(state.sent) s2.(state.sent).

  #[local] Existing Instance message.equiv_Equivalence.

  Lemma nle_refl s : nle s s.
  Proof.
    split.
    - intros f Hf. exact Hf.
    - intros a Ha. exists a. split; [exact Ha | reflexivity].
  Qed.

  Lemma knows_fact_of_implied K mhyps h :
    Forall (knows_meta_fact K) mhyps ->
    fact.implied_by_mfs mhyps h ->
    knows_fact K h.
  Proof.
    intros Hk Himp. apply Exists_exists in Himp. destruct Himp as (mh & Hmh & Himp).
    rewrite Forall_forall in Hk. specialize (Hk _ Hmh).
    destruct h as [nf | mf]; cbn [fact.implied_by_mf] in Himp.
    - destruct Himp as (Hm & Hc). destruct Hk as (_ & _ & _ & Hcons).
      apply (Hcons nf Hm). exact Hc.
    - subst. exact Hk.
  Qed.

  Lemma implied_of_knows_fact K mhyps h :
    Forall (knows_meta_fact K) mhyps ->
    fact.covered_by_pats (map meta_fact.pattern mhyps) h ->
    knows_fact K h ->
    fact.implied_by_mfs mhyps h.
  Proof.
    intros Hk Hcov Hh. cbv [fact.covered_by_pats] in Hcov. rewrite Exists_map in Hcov.
    apply Exists_exists in Hcov. destruct Hcov as (mh & Hmh & Hcov).
    apply Exists_exists. exists mh. split; [ exact Hmh | ].
    rewrite Forall_forall in Hk. specialize (Hk _ Hmh).
    destruct h as [nf | mf]; cbn [fact.covered_by fact.implied_by_mf knows_fact] in *.
    - destruct Hk as (_ & _ & _ & Hcons). split; [ exact Hcov | ].
      apply (Hcons nf Hcov). exact Hh.
    - destruct Hh as (_ & _ & _ & Hcons1). destruct Hk as (_ & _ & _ & Hcons2).
      apply meta_fact.eq_of_agree; [ symmetry; exact Hcov | ].
      intros nf Hm1 Hm2. rewrite (Hcons1 nf Hm1), (Hcons2 nf Hm2). reflexivity.
  Qed.

  Lemma claim_interp_nle t s c sf :
    star step init t s ->
    claim.interp name c sf.(state.sent) ->
    nle sf s ->
    claim.interp name c s.(state.sent).
  Proof.
    intros Hstar Hc (_ & Hincl). destruct c as [nf | pat]; cbn [claim.interp] in *.
    - destruct (Hincl _ Hc) as (b & Hb & Heq). cbn [message.equiv] in Heq. subst. exact Hb.
    - destruct Hc as (num & Hin & _). destruct (Hincl _ Hin) as (b & Hb & Heq).
      destruct b as [nf' | pat' src' num']; cbn [message.equiv] in Heq; [ discriminate | ].
      destruct Heq as [<- <-]. exists num'. split; [ exact Hb | ].
      eapply Existsn_ge_of_Existsn; [ eapply sent_counts_correct; eassumption | lia ].
  Qed.

  Lemma can_claim_normal K nf :
    can_claim K (claim.normal nf) ->
    Exists (fun r => can_deduce_normal_fact r K nf) p.(program.rules).
  Proof.
    intros (hyps & Hstep & Hhyps). invert Hstep.
    eapply Exists_impl; [ | eassumption ]. intros r Hr. exists hyps. split; assumption.
  Qed.

  Lemma can_claim_done K pat :
    can_claim K (claim.done_with pat) ->
    exists mf mr mhyps,
      mf.(meta_fact.pattern) = pat /\
        In mr p.(program.meta_rules) /\
        meta_rule.interp p.(program.rules) mr mf mhyps /\
        Forall (knows_meta_fact K) mhyps.
  Proof.
    intros (mf & hyps & <- & Hstep & Hhyps). invert Hstep.
    match goal with H : Exists _ _ |- _ => apply Exists_exists in H; destruct H as (mr & Hmr & Hint) end.
    exists mf, mr. eexists. ssplit; [ reflexivity | exact Hmr | exact Hint | ].
    rewrite Forall_map in Hhyps. exact Hhyps.
  Qed.

  Lemma normal_sent_or_step s nf :
    sent_dones_ok s ->
    Exists (fun r => can_deduce_normal_fact r s.(state.known) nf) p.(program.rules) ->
    In (message.normal nf) s.(state.sent) \/
      step s (O_event (message.label (message.normal nf)) [message.normal nf])
        {| state.known := s.(state.known); state.sent := message.normal nf :: s.(state.sent) |}.
  Proof.
    intros Hok Hex. destr (inb nf (filter_map message.as_normal s.(state.sent)));
      rewrite message.in_filter_map_as_normal in E.
    - left. exact E.
    - right. apply deduce_step. split; [ exact Hex | ].
      intros (pat & num & Hin & Hm). apply E.
      destruct (Hok _ _ Hin) as (_ & _ & _ & Hsat).
      apply Exists_exists in Hex. destruct Hex as (r & Hr & Hcdn).
      exact (Hsat r nf Hr Hcdn Hm).
  Qed.

  Definition normal_args_with (R : rel) (m : message) : option (list value) :=
    match m with
    | message.normal nf =>
        if eqb R nf.(normal_fact.rel) then Some nf.(normal_fact.args) else None
    | message.done_with _ _ _ => None
    end.

  Lemma In_normal_args_with R ms args :
    In args (filter_map (normal_args_with R) ms) <->
    In (message.normal {| normal_fact.rel := R; normal_fact.args := args |}) ms.
  Proof.
    rewrite in_filter_map. split.
    - intros ([nf | ] & Hin & Hargs); [|discriminate].
      destruct nf as [nrel nargs]. cbv [normal_args_with] in Hargs. simpl in Hargs.
      destr (eqb R nrel); [|discriminate]. invert Hargs. assumption.
    - intros Hin. eexists. split; [eassumption|]. cbv [normal_args_with].
      rewrite eqb_refl_true by assumption. reflexivity.
  Qed.

  Definition sent_meta_fact sent pat :=
    meta_fact.mk pat (filter_map (normal_args_with pat.(fact_pattern.rel)) sent).

  Lemma sent_meta_fact_consistent sent pat :
    meta_fact.consistent_with (sent_meta_fact sent pat) (knows_normal_fact sent).
  Proof.
    intros nf Hm. pose proof Hm as (Hrel & Hargs). cbv [sent_meta_fact knows_normal_fact].
    rewrite meta_fact.contains_mk, In_normal_args_with. destruct nf.
    cbn in Hrel, Hargs |- *. rewrite Hrel. tauto.
  Qed.

  Lemma sent_normal_deducible t s nf :
    star step init t s ->
    safe_inputs (flat_map inputs_of t) ->
    In (message.normal nf) s.(state.sent) ->
    Exists (fun r => can_deduce_normal_fact r s.(state.known) nf) p.(program.rules).
  Proof.
    induction 1; [ intros _ [] | ].
    intros Hsafe Hin.
    eapply safe_inputs_submultiset in Hsafe as Hsafe0; [ | apply submultiset_app_l ].
    invert H0; cbn [state.sent state.known] in *.
    - destruct Hin as [-> | Hin]; [ | auto ].
      eapply proj1. eassumption.
    - eapply Exists_impl; [ | apply IHstar; assumption ].
      intros r (hyps & Hri & Hk). exists hyps. split; [ exact Hri | ].
      eapply Forall_impl; [ exact Hk | ]. intros h Hh.
      eapply knows_fact_submultiset; [ apply submultiset_cons | | exact Hh ].
      rewrite (known_eq_inputs _ _ H). exact Hsafe.
  Qed.

  Local Abbreviation will_step := (will_step step safe_inputs).

  Context (Hmrv : program.meta_rules_valid p).

  Lemma step_preserves_sent_dones_ok s e s' :
    safe_inputs s'.(state.known) ->
    sent_dones_ok s ->
    step s e s' ->
    sent_dones_ok s'.
  Proof.
    intros Hallow Hok Hstep.
    invert Hstep; intros pat num Hin;
      cbn [can_deduce state.known state.sent] in Hallow, Hin |- *.
    - destruct Hin as [Hhead | Hin_old].
      + subst output. destruct H as (Hsrc & Hexmr & Hexn & Hsat).
        ssplit; [reflexivity | exact Hexmr | |].
        * apply Existsn_no; [intros [] | exact Hexn].
        * intros r nf Hr Hcdn Hm. cbn [state.known] in Hcdn.
          right. apply (Hsat r nf Hr Hcdn Hm).
      + specialize (Hok _ _ Hin_old). destruct Hok as (_ & Hexmr & Hexn & Hsat).
        ssplit; [reflexivity | exact Hexmr | |].
        * apply Existsn_no; [| exact Hexn].
          intros Hmatch. destruct output as [nf' | pat' src' cnt']; [| exact Hmatch].
          cbn [message.matches] in Hmatch.
          destruct H as (_ & Hfresh). apply Hfresh. exists pat, num. auto.
        * intros r nf Hr Hcdn Hm. cbn [state.known] in Hcdn.
          right. apply (Hsat r nf Hr Hcdn Hm).
    - specialize (Hok _ _ Hin). destruct Hok as (_ & Hexmr & Hexn & Hsat).
      ssplit; [reflexivity | | exact Hexn |].
      + eapply Exists_impl; [|exact Hexmr]. simpl. intros mr (mhyps & Hpi & Hkn).
        exists mhyps. split; [exact Hpi|].
        eapply Forall_impl; [exact Hkn|]. simpl. intros mh Hmh.
        exact (knows_fact_submultiset _ _ (fact.meta mh)
                 (submultiset_cons _ _) Hallow Hmh).
      + intros r nf Hr Hcdn Hm. cbn [state.known state.sent] in Hcdn |- *.
        apply Exists_exists in Hexmr. destruct Hexmr as (mr & Hmr & mhyps & Hpi & Hkn).
        destruct Hcdn as (hyps & Hri & Hkh).
        apply (Hsat r nf Hr); [| exact Hm].
        exists hyps. split; [exact Hri |].
        pose proof (Hmrv _ _ Hmr Hr _ _ _ _ Hpi Hri Hm) as Hcov.
        rewrite Forall_forall in Hkh, Hcov |- *. intros h Hh.
        eapply knows_fact_transfer_down_sub;
          [ apply submultiset_cons | exact Hallow | exact Hkn | eauto | eauto ].
  Qed.

  Lemma good_step s e s' t :
    good s t ->
    safe_inputs (flat_map inputs_of (e :: t)) ->
    step s e s' ->
    good s' (e :: t).
  Proof.
    intros (Hkeq & _ & Hok) Hallow' Hstep.
    assert (Hkeq' : s'.(state.known) = flat_map inputs_of (e :: t)).
    { invert Hstep; cbn [state.known]; rewrite Hkeq; reflexivity. }
    assert (Hak : safe_inputs s'.(state.known)) by (rewrite Hkeq'; exact Hallow').
    split; [exact Hkeq' | split; [exact Hallow' |]].
    eapply step_preserves_sent_dones_ok; eassumption.
  Qed.

  Lemma good_star s t t' s' :
    safe_inputs (flat_map inputs_of (t' ++ t)) ->
    good s t ->
    star step s t' s' ->
    good s' (t' ++ t).
  Proof.
    intros Hallow Hgood Hstar. revert Hallow.
    induction Hstar as [| t0 s'0 e s'' Hstar' IH Hstep]; intros Hallow.
    - exact Hgood.
    - assert (Hallow0 : safe_inputs (flat_map inputs_of (t0 ++ t))).
      { destruct e as [m | lbl outs].
        - eapply safe_inputs_submultiset; [apply submultiset_cons | exact Hallow].
        - exact Hallow. }
      exact (good_step s'0 e s'' (t0 ++ t) (IH Hallow0) Hallow Hstep).
  Qed.

  Lemma reachable_good t s :
    safe_inputs (flat_map inputs_of t) ->
    star step init t s ->
    good s t.
  Proof.
    intros Hallow Hstar.
    assert (good s (t ++ [])) as Hg.
    { eapply good_star;
        [ rewrite app_nil_r; exact Hallow | apply good_init | exact Hstar ]. }
    rewrite app_nil_r in Hg. exact Hg.
  Qed.

  Lemma will_match s1 lbl outs s1' s2 t2 :
    good s2 t2 ->
    step s1 (O_event lbl outs) s1' ->
    nle s1 s2 ->
    eventually will_step (fun '(s2', _) => nle s1' s2') (s2, t2).
  Proof.
    intros Hgood2 Hstep (Hki & Hsnle).
    invert Hstep. match goal with H : can_deduce _ _ |- _ => rename H into Hnf end.
    assert (Hmk : forall (X : state) o',
      knows_incl s1.(state.known) X.(state.known) ->
      submultiset s2.(state.sent) X.(state.sent) ->
      In o' X.(state.sent) -> message.equiv output o' ->
      nle {| state.known := s1.(state.known);
             state.sent := output :: s1.(state.sent) |} X).
    { intros X o' Hk Hs Ho'in Ho'eq. split.
      - cbn [state.known]. exact Hk.
      - cbn [state.sent]. intros a Ha. cbn [In] in Ha. destruct Ha as [Hao | Ha].
        + subst a. exists o'. split; [exact Ho'in | exact Ho'eq].
        + destruct (Hsnle a Ha) as (b & Hb & Hab). exists b. split; [| exact Hab].
          eapply submultiset_incl; [exact Hs | exact Hb]. }
    apply eventually_step_cps. cbn [will_step].
    exists (message.label output). intros sdem tdem Hstar Hallowdem.
    pose proof (good_star s2 t2 tdem sdem Hallowdem Hgood2 Hstar)
      as (Hkdem & Haldem & Hokdem).
    pose proof (step_star_mono s2 tdem sdem Hstar) as (Hkmono & Hsmono).
    assert (Halk : safe_inputs sdem.(state.known))
      by (rewrite Hkdem; exact Haldem).
    assert (Hki_dem : knows_incl s1.(state.known) sdem.(state.known))
      by (eapply knows_incl_grow; [ exact Hki | exact Hkmono | exact Halk ]).
    destruct output as [nf | pat osrc ocnt].
    - destruct Hnf as (Hex & _).
      apply Exists_exists in Hex. destruct Hex as (r & Hr_in & Hcdn1).
      destruct Hcdn1 as (hyps & Hri & Hknows1).
      assert (Hcdn_dem : can_deduce_normal_fact r sdem.(state.known) nf).
      { exists hyps. split; [exact Hri |].
        eapply Forall_impl; [exact Hknows1|]. simpl. intros h Hh. apply Hki_dem. exact Hh. }
      destr (inb nf (filter_map message.as_normal sdem.(state.sent)));
        rewrite message.in_filter_map_as_normal in E.
      + left. apply eventually_done. eapply Hmk; eauto. reflexivity.
      + right.
        exists {| state.known := sdem.(state.known);
                  state.sent := message.normal nf :: sdem.(state.sent) |},
               [message.normal nf].
        split.
        * apply deduce_step. cbn [can_deduce]. split.
          -- apply Exists_exists. eauto.
          -- intros (pat' & num' & Hinmeta & Hmatch').
             apply E.
             pose proof (Hokdem _ _ Hinmeta) as (_ & _ & _ & Hsat).
             exact (Hsat r nf Hr_in Hcdn_dem Hmatch').
        * apply eventually_done.
          apply (Hmk _ (message.normal nf)).
          -- cbn [state.known]. exact Hki_dem.
          -- cbn [state.sent].
             eapply submultiset_trans; [exact Hsmono | apply submultiset_cons].
          -- cbn [state.sent]. left. reflexivity.
          -- reflexivity.
    - destruct Hnf as (Hsrc & Hexmr & Hexn1 & Hsat1). subst osrc.
      pose proof (Existsn_length_filter _ _ sdem.(state.sent) (message.matchesb_spec pat)) as Hexn_d.
      set (num_d := length (filter (message.matchesb pat) sdem.(state.sent))) in Hexn_d.
      right.
      replace (message.label (message.done_with pat name ocnt))
        with (message.label (message.done_with pat name num_d)) by reflexivity.
      exists {| state.known := sdem.(state.known);
                state.sent := message.done_with pat name num_d :: sdem.(state.sent) |},
             [message.done_with pat name num_d].
      split.
      + apply deduce_step. cbn [can_deduce]. ssplit.
        * reflexivity.
        * eapply Exists_impl; [|exact Hexmr]. simpl.
          intros mr (mhyps & Hpi & Hkn). exists mhyps. split; [exact Hpi|].
          eapply Forall_impl; [exact Hkn|]. simpl. intros mh Hmh.
          apply (Hki_dem (fact.meta mh)). exact Hmh.
        * exact Hexn_d.
        * intros r'' nf Hr''_in Hcdn_dem Hmatch'.
          apply Exists_exists in Hexmr. destruct Hexmr as (mr & Hmr_in & mhyps & Hpi & Hkn).
          assert (Hcdn_s1 : can_deduce_normal_fact r'' s1.(state.known) nf).
          { destruct Hcdn_dem as (local_hyps & Hri & Hknown_new).
            exists local_hyps. split; [exact Hri |].
            pose proof (Hmrv _ _ Hmr_in Hr''_in _ _ _ _ Hpi Hri Hmatch') as Hcov.
            rewrite Forall_forall in Hknown_new, Hcov |- *.
            intros h Hh. eapply knows_fact_transfer_down;
              [ exact Hki_dem | exact Hkn | eauto | eauto ]. }
          pose proof (Hsat1 r'' nf Hr''_in Hcdn_s1 Hmatch') as Hin_s1.
          destruct (Hsnle _ Hin_s1) as (b & Hb & Hab).
          destruct b; cbn [message.equiv] in Hab; fwd; [|congruence].
          eapply submultiset_incl; eassumption.
      + apply eventually_done. eapply Hmk.
        * cbn [state.known]. exact Hki_dem.
        * cbn [state.sent].
          eapply submultiset_trans; [exact Hsmono | apply submultiset_cons].
        * cbn [state.sent]. left. reflexivity.
        * cbn [message.equiv]. auto.
  Qed.

  Lemma drive_to_dominate t0 s0 t' sf :
    star step init t0 s0 ->
    safe_inputs (flat_map inputs_of t0) ->
    star step s0 t' sf ->
    flat_map inputs_of t' = [] ->
    eventually will_step (fun '(s2, _) => nle sf s2) (s0, t0).
  Proof.
    intros Hstar0 Hga0 Hrun Hinp. revert Hinp.
    induction Hrun as [| T0 smid e sf' Hrun' IH Hstep]; intros Hinp.
    - apply eventually_done. apply nle_refl.
    - destruct e as [m | lbl outs].
      + cbn [inputs_of flat_map app] in Hinp. discriminate Hinp.
      + cbn [inputs_of flat_map app] in Hinp. specialize (IH Hinp).
        apply eventually_will_step_annotate in IH.
        eapply eventually_trans; [exact IH |].
        intros [s2 t2] (Hreach & Hle_mid).
        destruct Hreach as (tr & Hstar_s0s2 & -> & Hga_imp).
        specialize (Hga_imp Hga0).
        assert (Hstar2 : star step init (tr ++ t0) s2) by eauto using star_app.
        eapply will_match; try eassumption.
        eapply reachable_good; eassumption.
  Qed.

  Lemma send_all s L :
    sent_dones_ok s ->
    safe_inputs s.(state.known) ->
    Forall (fun nf => Exists (fun r => can_deduce_normal_fact r s.(state.known) nf) p.(program.rules)) L ->
    exists t' s',
      star step s t' s' /\ flat_map inputs_of t' = [] /\
        s'.(state.known) = s.(state.known) /\ sent_dones_ok s' /\
        Forall (fun nf => In (message.normal nf) s'.(state.sent)) L.
  Proof.
    revert s. induction L as [|nf L IH]; intros s Hok Hsafe HL.
    - exists [], s. ssplit; auto using star_refl.
    - apply Forall_cons_iff in HL. destruct HL as [Hnf HL].
      destruct (normal_sent_or_step s nf Hok Hnf) as [Hin | Hstep].
      + destruct (IH s Hok Hsafe HL) as (t' & s' & Hstar & Hinp & Hk & Hok' & Hall).
        exists t', s'. ssplit; [ assumption .. | ].
        constructor; [ | assumption ].
        eapply submultiset_incl; [ apply (step_star_mono _ _ _ Hstar) | exact Hin ].
      + assert (Hok1 : sent_dones_ok {| state.known := s.(state.known);
                                         state.sent := message.normal nf :: s.(state.sent) |})
          by (eapply step_preserves_sent_dones_ok; eassumption).
        destruct (IH _ Hok1 Hsafe HL) as (t' & s' & Hstar & Hinp & Hk & Hok' & Hall).
        exists (t' ++ [O_event (message.label (message.normal nf)) [message.normal nf]]), s'.
        ssplit.
        * eapply star_app; [ apply star_one; exact Hstep | exact Hstar ].
        * rewrite flat_map_app, Hinp. reflexivity.
        * exact Hk.
        * exact Hok'.
        * constructor; [ | assumption ].
          eapply submultiset_incl; [ apply (step_star_mono _ _ _ Hstar) | left; reflexivity ].
  Qed.

  Lemma send_all_saturated s mf mr mhyps :
    In mr p.(program.meta_rules) ->
    meta_rule.interp p.(program.rules) mr mf mhyps ->
    Forall (knows_meta_fact s.(state.known)) mhyps ->
    Forall (fun nf => In (message.normal nf) s.(state.sent)) (meta_fact.normal_facts mf) ->
    saturated s mf.(meta_fact.pattern).
  Proof.
    intros Hmr (Hpi & Hset) Hmh Hall r nf Hr (hyps & Hri & Hhyps) Hm.
    rewrite Forall_forall in Hall. apply Hall, meta_fact.in_normal_facts. split; [ exact Hm | ].
    apply (Hset nf Hm). exists hyps. split; [ apply Exists_exists; eauto | ].
    pose proof (Hmrv _ _ Hmr Hr _ _ _ _ Hpi Hri Hm) as Hcov.
    rewrite Forall_forall in Hhyps, Hcov |- *. intros h Hh.
    apply implied_of_knows_fact with (K := s.(state.known)); auto.
  Qed.

  Lemma can_claim_run t st c :
    star step init t st ->
    safe_inputs (flat_map inputs_of t) ->
    can_claim (flat_map inputs_of t) c ->
    exists t' sf,
      star step st t' sf /\ flat_map inputs_of t' = [] /\ claim.interp name c sf.(state.sent).
  Proof.
    intros Hstar Hsafe Hc.
    destruct (reachable_good _ _ Hsafe Hstar) as (Hk & _ & Hok).
    rewrite <- Hk in Hsafe, Hc.
    destruct c as [nf | pat].
    - apply can_claim_normal in Hc.
      destruct (send_all st [nf] Hok Hsafe) as (t' & sf & Hrun & Hinp & _ & _ & Hall).
      { constructor; [ exact Hc | constructor ]. }
      exists t', sf. ssplit; [ assumption | assumption | ].
      apply Forall_inv in Hall. exact Hall.
    - apply can_claim_done in Hc. destruct Hc as (mf & mr & mhyps & <- & Hmr & Hint & Hmh).
      pose proof Hint as (Hpi & Hset).
      destruct (send_all st (meta_fact.normal_facts mf) Hok Hsafe)
        as (t' & s' & Hrun & Hinp & Hk' & _ & Hall).
      { rewrite Forall_forall. intros nf Hnf. apply meta_fact.in_normal_facts in Hnf.
        destruct Hnf as (Hm & Hc). apply (Hset nf Hm) in Hc. destruct Hc as (hyps & Hex & Hhyps).
        eapply Exists_impl; [ | exact Hex ]. intros r Hr. exists hyps. split; [ exact Hr | ].
        eapply Forall_impl; [ exact Hhyps | ]. intros h Hh. eapply knows_fact_of_implied; eassumption. }
      set (num := length (filter (message.matchesb mf.(meta_fact.pattern)) s'.(state.sent))).
      assert (Hnum : Existsn (message.matches mf.(meta_fact.pattern)) num s'.(state.sent))
        by (apply Existsn_length_filter; exact (message.matchesb_spec _)).
      exists (O_event (message.label (message.done_with mf.(meta_fact.pattern) name num))
                      [message.done_with mf.(meta_fact.pattern) name num] :: t'),
        {| state.known := s'.(state.known);
           state.sent := message.done_with mf.(meta_fact.pattern) name num :: s'.(state.sent) |}.
      ssplit.
      + eapply star_step; [ exact Hrun | ]. apply deduce_step. cbn [can_deduce]. ssplit.
        * reflexivity.
        * apply Exists_exists. exists mr. split; [ exact Hmr | ].
          exists mhyps. split; [ exact Hpi | ]. rewrite Hk'. exact Hmh.
        * exact Hnum.
        * eapply send_all_saturated; [ exact Hmr | exact Hint | rewrite Hk'; exact Hmh | exact Hall ].
      + cbn. exact Hinp.
      + exists num. split; [ left; reflexivity | ].
        apply Eg_skip. eapply Existsn_ge_of_Existsn; [ exact Hnum | lia ].
  Qed.

  Lemma can_claim_sound c t st :
    can_claim (flat_map inputs_of t) c ->
    safe_inputs (flat_map inputs_of t) ->
    star step init t st ->
    eventually will_step (fun '(_, t') => claim.interp name c (flat_map outputs_of t')) (st, t).
  Proof.
    intros Hc Hsafe Hstar.
    destruct (can_claim_run _ _ _ Hstar Hsafe Hc) as (t' & sf & Hrun & Hinp & Hsf).
    eapply eventually_weaken.
    { apply eventually_will_step_annotate. eapply drive_to_dominate; eassumption. }
    intros [s2 t2] ((tr & Hstar2 & -> & _) & Hle). cbv beta iota.
    rewrite <- (sent_eq_outputs (tr ++ t) s2) by (eapply star_app; eassumption).
    eapply claim_interp_nle; [ eapply star_app; eassumption | eassumption | eassumption ].
  Qed.

  Lemma can_claim_conj_sound Ps t st :
    can_claim_conj (flat_map inputs_of t) Ps ->
    safe_inputs (flat_map inputs_of t) ->
    star step init t st ->
    eventually will_step (fun '(_, t') => claim.interp_conj name Ps (flat_map outputs_of t')) (st, t).
  Proof.
    intros HPs Hsafe Hstar. eapply eventually_weaken.
    - apply eventually_will_step_Forall with (Ps := map (fun P '(_, t') => claim.interp name P (flat_map outputs_of t')) Ps).
      + rewrite Forall_map. apply Forall_forall. intros P _ s s' e t' HP _.
        eapply claim.interp_mono; [ exact HP | apply submultiset_app_l ].
      + rewrite Forall_map. eapply Forall_impl; [ exact HPs | ].
        intros. eapply can_claim_sound; eassumption.
    - intros [s' t'] H. cbv beta in H. rewrite Forall_map in H. exact H.
  Qed.

  Lemma can_claim_complete t st c :
    star step init t st ->
    safe_inputs (flat_map inputs_of t) ->
    claim.interp name c (flat_map outputs_of t) ->
    can_claim (flat_map inputs_of t) c.
  Proof.
    intros Hstar Hsafe Hc.
    destruct (reachable_good _ _ Hsafe Hstar) as (Hk & _ & Hok).
    rewrite <- (sent_eq_outputs _ _ Hstar) in Hc. rewrite <- Hk.
    destruct c as [nf | pat]; cbn [claim.interp can_claim] in *.
    - pose proof (sent_normal_deducible _ _ _ Hstar Hsafe Hc) as Hex.
      apply Exists_exists in Hex. destruct Hex as (r & Hr & hyps & Hri & Hhyps).
      exists hyps. split; [ | exact Hhyps ].
      constructor. apply Exists_exists. eauto.
    - destruct Hc as (num & Hin & _).
      destruct (Hok _ _ Hin) as (_ & Hexmr & _ & Hsat).
      apply Exists_exists in Hexmr. destruct Hexmr as (mr & Hmr & mhyps & Hpi & Hmh).
      exists (sent_meta_fact st.(state.sent) pat), (map fact.meta mhyps). ssplit.
      + reflexivity.
      + constructor. apply Exists_exists. exists mr. split; [ exact Hmr | ].
        split; [ exact Hpi | ]. intros nf Hm.
        rewrite (sent_meta_fact_consistent _ _ nf Hm). split.
        * intros Hnf. pose proof (sent_normal_deducible _ _ _ Hstar Hsafe Hnf) as Hex.
          apply Exists_exists in Hex. destruct Hex as (r & Hr & hyps & Hri & Hhyps).
          exists hyps. split; [ apply Exists_exists; eauto | ].
          pose proof (Hmrv _ _ Hmr Hr _ _ _ _ Hpi Hri Hm) as Hcov.
          rewrite Forall_forall in Hhyps, Hcov |- *. intros h Hh.
          apply implied_of_knows_fact with (K := st.(state.known)); auto.
        * intros (hyps & Hex & Himp). apply Exists_exists in Hex. destruct Hex as (r & Hr & Hri).
          apply (Hsat r nf Hr); [ | exact Hm ].
          exists hyps. split; [ exact Hri | ].
          eapply Forall_impl; [ exact Himp | ]. intros h Hh. eapply knows_fact_of_implied; eassumption.
      + rewrite Forall_map. exact Hmh.
  Qed.

  Lemma can_claim_conj_complete t st Ps :
    star step init t st ->
    safe_inputs (flat_map inputs_of t) ->
    claim.interp_conj name Ps (flat_map outputs_of t) ->
    can_claim_conj (flat_map inputs_of t) Ps.
  Proof.
    intros Hstar Hsafe HPs. eapply Forall_impl; [ exact HPs | ].
    intros. cbv beta in *. eapply can_claim_complete; eassumption.
  Qed.

  Context (Hsenders : forall R, In R (program.normal_concl_rels p) -> In name (R_senders R)).

  Lemma sent_rel_sender t s nf :
    star step init t s ->
    In (message.normal nf) s.(state.sent) ->
    In name (R_senders nf.(normal_fact.rel)).
  Proof.
    induction 1; [ destruct 1 | ].
    intros Hin. invert H0; cbn [state.sent] in Hin; [ | auto ].
    destruct Hin as [-> | Hin]; [ | auto ].
    apply Hsenders. eapply can_deduce_normal_concl_rel. eassumption.
  Qed.

  Lemma safe_preserved t st :
    star step init t st ->
    safe_output (flat_map outputs_of t).
  Proof.
    intros Hstar. rewrite <- (sent_eq_outputs _ _ Hstar). split.
    - intros pat src cnt Hin.
      replace src with name in * by (symmetry; eapply sent_source_correct; eassumption).
      split; [ reflexivity | ].
      eapply Existsn_le_of_Existsn; [ eapply sent_counts_correct; eassumption | lia ].
    - intros nf Hin. eapply sent_rel_sender; eassumption.
  Qed.

  Lemma can_claim_mono_inc inps c inps' :
    can_claim inps c ->
    safe_inputs inps' ->
    submultiset inps inps' ->
    can_claim inps' c.
  Proof.
    intros Hc Hsafe Hsub. destruct c; cbv [can_claim] in *; fwd.
    - eexists. split; [ eassumption | ].
      eapply Forall_impl; [ eassumption | ]. intros. eapply knows_fact_submultiset; eassumption.
    - do 2 eexists. ssplit; [ reflexivity | eassumption | ].
      eapply Forall_impl; [ eassumption | ]. intros. eapply knows_fact_submultiset; eassumption.
  Qed.

  Lemma can_claim_conj_mono_inc inps Ps inps' :
    can_claim_conj inps Ps ->
    safe_inputs inps' ->
    submultiset inps inps' ->
    can_claim_conj inps' Ps.
  Proof.
    intros HPs Hsafe Hsub. eapply Forall_impl; [ exact HPs | ].
    intros. eapply can_claim_mono_inc; eassumption.
  Qed.
End __.
End node.
