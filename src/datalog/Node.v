From Stdlib Require Import List Lia Permutation Classical_Prop RelationClasses.
From Datalog Require Import List Datalog Smallstep Tactics Graph.
From coqutil Require Import Map.Interface.
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
    Context `{params : datalog_params} {sender_label : sender_labelT}.

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

    Definition normal_facts (f : message) : list normal_fact :=
      match f with
      | normal nf => [nf]
      | done_with _ _ _ => []
      end.

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

Module state.
  Section __.
    Context `{params : datalog_params} {sender_label : sender_labelT}.

    Record state :=
      { known : list message;
        sent : list message }.
  End __.
End state. Abbreviation state := state.state.

Section __.
  Context `{params : datalog_params} {sender_label : sender_labelT}.
  Context (R_senders : rel -> list sender_label).

  Definition knows_normal_fact (known : list message) (nf : normal_fact) :=
    In (message.normal nf) known.

  Definition expects_num_facts (known : list message) (pat : fact_pattern) num :=
    exists expected_msgss,
      Forall2 (fun n expected_msgs => In (message.done_with pat n expected_msgs) known)
        (R_senders pat.(fact_pattern.rel)) expected_msgss /\
        num = list_sum expected_msgss.

  Definition knows_meta_fact (known : list message) (mf : meta_fact) :=
    exists num,
      expects_num_facts known mf.(meta_fact.pattern) num /\
        Existsn (message.matches mf.(meta_fact.pattern)) num known /\
        fact.set_consistent_with mf (knows_normal_fact known).

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

  Definition sends_concl_rels (nm : sender_label) (p : program) :=
    forall R, In R (program.concl_rels p) -> In nm (R_senders R).

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

  Definition allowed_inputs (inputs : list message) :=
    forall pat expected_msgss,
      Forall2 (fun k e => In (message.done_with pat k e) inputs)
              (R_senders pat.(fact_pattern.rel)) expected_msgss ->
      Existsn_le (message.matches pat) (list_sum expected_msgss) inputs.

  Definition init : state :=
    {| state.known := []; state.sent := [] |}.

  Definition claim (pat : fact_pattern) (l : list message) :=
    forall src, In src (R_senders pat.(fact_pattern.rel)) ->
      exists cnt, In (message.done_with pat src cnt) l.

  Definition consistent (pat : fact_pattern) (known : list message) : Prop :=
    exists num, expects_num_facts known pat num /\
             Existsn_ge (message.matches pat) num known.

  Definition nle (s1 s2 : state) :=
    consistently_incl message.equiv claim consistent s1.(state.known) s2.(state.known) /\
      incl_mod message.equiv s1.(state.sent) s2.(state.sent).

  Local Abbreviation will_step := (will_step step allowed_inputs).

  (*every done-message this node has sent could still be deduced now*)
  Definition sent_dones_ok (s : state) : Prop :=
    forall pat num,
      In (message.done_with pat name num) s.(state.sent) ->
      can_deduce s (message.done_with pat name num)
  (*not clear whether we need this next conjunct.  we could get it,
    by saying something like "inputs are consistent outputs from other nodes,
    plus the outputs of this node."
    not sure if that will later become necessary.
   *)
  (*/\
          (forall mf_set, ~ In (meta_fact R mf_args mf_set) hyps)*).

  Definition good (s : state) (t : list IO_event) :=
    s.(state.known) = flat_map inputs_of t /\
    allowed_inputs (flat_map inputs_of t) /\
    sent_dones_ok s.

  #[local] Existing Instance message.equiv_Equivalence.

  Lemma allowed_inputs_submultiset l1 l2 :
    submultiset l1 l2 -> allowed_inputs l2 -> allowed_inputs l1.
  Proof.
    intros Hsub Hbound pat ems Hf2.
    pose proof (submultiset_incl _ _ Hsub) as Hincl.
    assert (Hf2' : Forall2 (fun k e => In (message.done_with pat k e) l2)
                           (R_senders pat.(fact_pattern.rel)) ems)
      by (clear -Hf2 Hincl; induction Hf2; constructor;
            [apply Hincl; assumption | assumption]).
    eapply Existsn_le_submultiset; [ apply Hbound; exact Hf2' | exact Hsub ].
  Qed.

  Lemma submultiset_rest_no_matches pat small rest big num :
    Permutation big (small ++ rest) ->
    allowed_inputs big ->
    expects_num_facts small pat num ->
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
    submultiset l1 l2 -> allowed_inputs l2 ->
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

  Lemma knows_fact_transfer_down_sub small big mhyps h :
    submultiset small big ->
    allowed_inputs big ->
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
      rewrite Hcov in Hexp_h, Hex_h, Hrest_no.
      exists num_h. split; [exact Hexp_h | split; [exact Hex_h |]].
      intros nf Hm. specialize (Hiff_new nf Hm). split.
      + intro Hset. apply Hiff_new in Hset.
        pose proof (Permutation_in _ Hperm Hset) as Hin_app.
        apply in_app_or in Hin_app. destruct Hin_app as [Hin | Hinr]; [exact Hin |].
        exfalso. apply (Hrest_no _ Hinr). exact Hm.
      + intro Hin. apply Hiff_new. apply Hincl. exact Hin.
  Qed.

  Lemma step_preserves_sent_dones_ok s e s' :
    program.meta_rules_valid p ->
    allowed_inputs s'.(state.known) ->
    sent_dones_ok s ->
    step s e s' ->
    sent_dones_ok s'.
  Proof.
    intros Hmrv Hallow Hok Hstep.
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
    program.meta_rules_valid p ->
    good s t ->
    allowed_inputs (flat_map inputs_of (e :: t)) ->
    step s e s' ->
    good s' (e :: t).
  Proof.
    intros Hmrv (Hkeq & _ & Hok) Hallow' Hstep.
    assert (Hkeq' : s'.(state.known) = flat_map inputs_of (e :: t)).
    { invert Hstep; cbn [state.known]; rewrite Hkeq; reflexivity. }
    assert (Hak : allowed_inputs s'.(state.known)) by (rewrite Hkeq'; exact Hallow').
    split; [exact Hkeq' | split; [exact Hallow' |]].
    eapply step_preserves_sent_dones_ok; eassumption.
  Qed.

  Lemma good_init : good init [].
  Proof.
    split; [reflexivity | split].
    - intros pat ems _. apply El_nil.
    - intros pat num H. destruct H.
  Qed.

  Lemma good_star s t t' s' :
    program.meta_rules_valid p ->
    allowed_inputs (flat_map inputs_of (t' ++ t)) ->
    good s t ->
    star step s t' s' ->
    good s' (t' ++ t).
  Proof.
    intros Hmrv Hallow Hgood Hstar. revert Hallow.
    induction Hstar as [| t0 s'0 e s'' Hstar' IH Hstep]; intros Hallow.
    - exact Hgood.
    - assert (Hallow0 : allowed_inputs (flat_map inputs_of (t0 ++ t))).
      { destruct e as [m | lbl outs].
        - eapply allowed_inputs_submultiset; [apply submultiset_cons | exact Hallow].
        - exact Hallow. }
      exact (good_step s'0 e s'' (t0 ++ t) Hmrv (IH Hallow0) Hallow Hstep).
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

  Lemma driven_inputs_submultiset t0 s0 tr s2 :
    star step init t0 s0 ->
    star step s0 tr s2 ->
    submultiset (flat_map inputs_of t0) s2.(state.known).
  Proof.
    intros Hstar Hstar2.
    rewrite <- (known_eq_inputs t0 s0 Hstar).
    exact (proj1 (step_star_mono s0 tr s2 Hstar2)).
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

  Lemma expects_num_facts_incl pat l1 l2 num :
    expects_num_facts l1 pat num -> incl l1 l2 ->
    expects_num_facts l2 pat num.
  Proof. cbv [expects_num_facts]. intros. fwd. eauto using Forall2_impl. Qed.

  #[local] Hint Resolve expects_num_facts_incl Existsn_ge_submultiset
    Existsn_le_submultiset submultiset_incl incl_def : core.

  Lemma consistent_mono pat ms1 ms2 :
    consistent pat ms1 -> submultiset ms1 ms2 -> consistent pat ms2.
  Proof. cbv [consistent]. intros. fwd. eauto 6. Qed.

  Lemma claim_mono pat ms1 ms2 :
    claim pat ms1 -> incl_mod message.equiv ms1 ms2 -> claim pat ms2.
  Proof.
    cbv [claim]. intros H Hincl. fwd.
    intros. especialize H; eauto. fwd.
    cbv [incl_mod] in Hincl. especialize Hincl; eauto. fwd.
    destruct b; cbn [message.equiv] in Hinclp1; fwd; [congruence | eauto].
  Qed.

  Lemma consistently_incl_of_submultiset l1 l2 :
    submultiset l1 l2 -> consistently_incl message.equiv claim consistent l1 l2.
  Proof.
    intros Hsub. split.
    - exact (incl_mod_of_submultiset message.equiv _ _ Hsub).
    - intros pat _ Hc. eapply consistent_mono; [ exact Hc | exact Hsub ].
  Qed.

  Definition knows_incl (l1 l2 : list message) : Prop :=
    forall f, knows_fact l1 f -> knows_fact l2 f.

  Lemma knows_incl_of_submultiset l1 l2 :
    submultiset l1 l2 -> allowed_inputs l2 -> knows_incl l1 l2.
  Proof. intros Hsub Hallow f. apply knows_fact_submultiset; assumption. Qed.

  Lemma knows_incl_grow l1 l2 l2' :
    knows_incl l1 l2 -> submultiset l2 l2' -> allowed_inputs l2' -> knows_incl l1 l2'.
  Proof.
    intros Hki Hsub Hallow f Hf.
    eapply knows_fact_submultiset; [ exact Hsub | exact Hallow | apply Hki; exact Hf ].
  Qed.

  Lemma consistently_incl_trans l1 l2 l3 :
    consistently_incl message.equiv claim consistent l1 l2 ->
    consistently_incl message.equiv claim consistent l2 l3 ->
    consistently_incl message.equiv claim consistent l1 l3.
  Proof.
    intros (Hi1 & Hc1) (Hi2 & Hc2). split.
    - exact (incl_mod_trans message.equiv l1 l2 l3 Hi1 Hi2).
    - intros pat Hcl Hco.
      apply Hc2; [ eapply claim_mono; [ exact Hcl | exact Hi1 ] | apply Hc1; assumption ].
  Qed.

  Lemma incl_mod_normal_In l1 l2 nf :
    incl_mod message.equiv l1 l2 ->
    In (message.normal nf) l1 -> In (message.normal nf) l2.
  Proof.
    intros Hincl Hin. destruct (Hincl _ Hin) as (b & Hb & Heq).
    cbn [message.equiv] in Heq. destruct b; fwd; [exact Hb | congruence].
  Qed.

  Lemma knows_fact_consistently_incl l1 l2 h :
    consistently_incl message.equiv claim consistent l1 l2 ->
    noncontradictory_wf message.equiv claim consistent allowed_inputs l1 l2 ->
    allowed_inputs l2 ->
    knows_fact l1 h -> knows_fact l2 h.
  Proof.
    intros (Hincl12 & Hcle12) Hnc Hallow2 Hk.
    destruct Hnc as [m Hsub1m Hallowm (Hincl2m & _) _].
    destruct h as [nf | mf].
    - exact (incl_mod_normal_In _ _ _ Hincl12 Hk).
    - pose proof (knows_fact_submultiset l1 m (fact.meta mf) Hsub1m Hallowm Hk) as Hkm.
      destruct Hk as (num & Hexp & Hexn & Hiff).
      destruct Hkm as (_ & _ & _ & Hiffm).
      assert (Hclaim1 : claim mf.(meta_fact.pattern) l1).
      { intros src Hsrc. destruct Hexp as (ems & Hf2 & _).
        destruct (Forall2_In_l _ _ _ _ Hf2 Hsrc) as (e & _ & Hin). exists e. exact Hin. }
      assert (Hcons1 : consistent mf.(meta_fact.pattern) l1).
      { exists num. split; [ exact Hexp | ].
        eapply Existsn_ge_of_Existsn; [ exact Hexn | lia ]. }
      destruct (Hcle12 mf.(meta_fact.pattern) Hclaim1 Hcons1) as (N & HexpN & HgeN).
      destruct HexpN as (emsN & Hf2N & HsumN).
      pose proof (Hallow2 mf.(meta_fact.pattern) emsN Hf2N) as HleN.
      rewrite <- HsumN in HleN.
      exists N. ssplit.
      + exists emsN. auto.
      + apply Existsn_of_ge_le; [ exact HgeN | exact HleN ].
      + intros nf Hm. split.
        * intro Hset. exact (incl_mod_normal_In _ _ _ Hincl12 (proj1 (Hiff nf Hm) Hset)).
        * intro Hin2. exact (proj2 (Hiffm nf Hm) (incl_mod_normal_In _ _ _ Hincl2m Hin2)).
  Qed.

  Lemma knows_incl_of_consistently_incl l1 l2 :
    consistently_incl message.equiv claim consistent l1 l2 ->
    noncontradictory_wf message.equiv claim consistent allowed_inputs l1 l2 ->
    allowed_inputs l2 -> knows_incl l1 l2.
  Proof. intros Hci Hnc Hallow f. apply knows_fact_consistently_incl; assumption. Qed.

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
      rewrite Hcov in Hexp_s, Hex_s.
      exists num_s. split; [ exact Hexp_s | split; [ exact Hex_s | ] ].
      intros nf Hm.
      assert (Hm' : fact_pattern.matches mh.(meta_fact.pattern) nf)
        by (rewrite Hcov; exact Hm).
      specialize (Hiff_s nf Hm'). specialize (Hiff_b nf Hm). specialize (Hiff_b' nf Hm').
      cbv [knows_normal_fact] in *. tauto.
  Qed.

  Lemma will_match s1 lbl outs s1' s2 t2 :
    program.meta_rules_valid p ->
    good s2 t2 ->
    step s1 (O_event lbl outs) s1' ->
    nle s1 s2 ->
    knows_incl s1.(state.known) s2.(state.known) ->
    eventually will_step (fun '(s2', _) => nle s1' s2') (s2, t2).
  Proof.
    intros Hmrv Hgood2 Hstep (Hknle & Hsnle) Hki.
    invert Hstep. rename H3 into Hnf.
    assert (Hmk : forall (X : state) o',
      consistently_incl message.equiv claim consistent s1.(state.known) X.(state.known) ->
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
    pose proof (good_star s2 t2 tdem sdem Hmrv Hallowdem Hgood2 Hstar)
      as (Hkdem & Haldem & Hokdem).
    pose proof (step_star_mono s2 tdem sdem Hstar) as (Hkmono & Hsmono).
    assert (HconK : consistently_incl message.equiv claim consistent
                      s1.(state.known) sdem.(state.known))
      by (eapply consistently_incl_trans;
            [exact Hknle | apply consistently_incl_of_submultiset; exact Hkmono]).
    assert (Halk : allowed_inputs sdem.(state.known))
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
      destruct (classic (In (message.normal nf) sdem.(state.sent))) as [Hin | Hnin].
      + left. apply eventually_done. eapply Hmk; eauto. reflexivity.
      + right.
        exists {| state.known := sdem.(state.known);
                  state.sent := message.normal nf :: sdem.(state.sent) |},
               [message.normal nf].
        split.
        * apply deduce_step. cbn [can_deduce]. split.
          -- apply Exists_exists. eauto.
          -- intros (pat' & num' & Hinmeta & Hmatch').
             apply Hnin.
             pose proof (Hokdem _ _ Hinmeta) as (_ & _ & _ & Hsat).
             exact (Hsat r nf Hr_in Hcdn_dem Hmatch').
        * apply eventually_done.
          apply (Hmk _ (message.normal nf)).
          -- cbn [state.known]. exact HconK.
          -- cbn [state.sent].
             eapply submultiset_trans; [exact Hsmono | apply submultiset_cons].
          -- cbn [state.sent]. left. reflexivity.
          -- reflexivity.
    - destruct Hnf as (Hsrc & Hexmr & Hexn1 & Hsat1). subst osrc.
      destruct (Existsn_total (message.matches pat) sdem.(state.sent))
        as (num_d & Hexn_d).
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
        * cbn [state.known]. exact HconK.
        * cbn [state.sent].
          eapply submultiset_trans; [exact Hsmono | apply submultiset_cons].
        * cbn [state.sent]. left. reflexivity.
        * cbn [message.equiv]. auto.
  Qed.

  Lemma nle_refl s : nle s s.
  Proof.
    split; [ exact (consistently_incl_refl message.equiv claim consistent _) | ].
    intros a Ha. exists a. split; [exact Ha | reflexivity].
  Qed.

  Ltac inv_step :=
    match goal with
    | H: step _ _ _ |- _ => invert H
    end.

  Lemma sent_eq_outputs t s :
    star step init t s -> s.(state.sent) = flat_map outputs_of t.
  Proof.
    intros Hstar. induction Hstar; eauto.
    inv_step; simpl; eauto. f_equal. auto.
  Qed.

  Lemma sent_source_correct t s :
    star step init t s ->
    forall pat src num,
      In (message.done_with pat src num) s.(state.sent) -> src = name.
  Proof.
    induction 1 as [| t0 s' e s'' Hstar IH Hstep]; intros pat src num Hin.
    - destruct Hin.
    - invert Hstep; cbn [state.sent] in Hin |- *.
      + destruct Hin as [Hhead | Hin_old]; [| exact (IH _ _ _ Hin_old)].
        subst output. destruct H as (Hsrc & _). exact Hsrc.
      + exact (IH _ _ _ Hin).
  Qed.

  Lemma sent_counts_correct t s :
    star step init t s ->
    forall pat num,
      In (message.done_with pat name num) s.(state.sent) ->
      Existsn (message.matches pat) num s.(state.sent).
  Proof.
    induction 1 as [| t0 s' e s'' Hstar IH Hstep]; intros pat num Hin.
    - destruct Hin.
    - invert Hstep; cbn [state.sent] in Hin |- *.
      + destruct Hin as [Hhead | Hin_old].
        * subst output. destruct H as (_ & _ & Hexn & _).
          apply Existsn_no; [intros [] | exact Hexn].
        * apply Existsn_no; [ | exact (IH _ _ Hin_old) ].
          intros Hmatch. destruct output as [nf' | pat' src' cnt']; [| exact Hmatch].
          cbn [message.matches] in Hmatch.
          destruct H as (_ & Hfresh). apply Hfresh. exists pat, num. auto.
      + exact (IH _ _ Hin).
  Qed.

  Lemma can_deduce_concl_rel ns m :
    can_deduce ns m -> In (message.rel m) (program.concl_rels p).
  Proof.
    destruct m as [nf | pat src num]; cbn [can_deduce message.rel].
    - intros (Hex & _). apply Exists_exists in Hex.
      destruct Hex as (r & Hr & hyps & Hri & _).
      eapply program.rule_concl_rel_in; eauto using rule.interp_concl_relname_in.
    - intros (_ & Hex & _). apply Exists_exists in Hex.
      destruct Hex as (mr & Hmr & mhyps & Hpi & _).
      eapply program.meta_rule_concl_rel_in;
        eauto using meta_rule.pattern_interp_concl_relname_in.
  Qed.

  Lemma sent_rel_sender t s :
    (forall s0 f, can_deduce s0 f -> In name (R_senders (message.rel f))) ->
    star step init t s ->
    forall f, In f s.(state.sent) -> In name (R_senders (message.rel f)).
  Proof.
    intros Hsend Hstar.
    induction Hstar as [| t0 s' e s'' Hstar IH Hstep]; intros f Hin.
    - destruct Hin.
    - invert Hstep; cbn [state.sent] in Hin.
      + destruct Hin as [Hhead | Hin_old].
        * subst output. exact (Hsend s' f H).
        * exact (IH f Hin_old).
      + exact (IH f Hin).
  Qed.

  Lemma reachable_good t s :
    program.meta_rules_valid p ->
    allowed_inputs (flat_map inputs_of t) ->
    star step init t s ->
    good s t.
  Proof.
    intros Hmrv Hallow Hstar.
    assert (good s (t ++ [])) as Hg.
    { eapply good_star;
        [ exact Hmrv | rewrite app_nil_r; exact Hallow | apply good_init | exact Hstar ]. }
    rewrite app_nil_r in Hg. exact Hg.
  Qed.

  Lemma drive_to_dominate t0 s0 t' sf :
    program.meta_rules_valid p ->
    star step init t0 s0 ->
    allowed_inputs (flat_map inputs_of t0) ->
    star step s0 t' sf ->
    flat_map inputs_of t' = [] ->
    eventually will_step (fun '(s2, _) => nle sf s2) (s0, t0).
  Proof.
    intros Hmrv Hstar0 Hga0 Hrun Hinp. revert Hinp.
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
        { eapply reachable_good; eassumption. }
        apply knows_incl_of_submultiset.
        { rewrite (known_input_free s0 T0 smid Hrun' Hinp).
          exact (proj1 (step_star_mono s0 tr s2 Hstar_s0s2)). }
        rewrite (known_eq_inputs (tr ++ t0) s2 Hstar2). exact Hga_imp.
  Qed.

  Lemma might_implies_will :
    program.meta_rules_valid p ->
    might_implies_will_equiv step message.equiv allowed_inputs init.
  Proof.
    intros Hmrv t s o Hstar Hallow (t' & sf & Hrun & Hinp & Hino).
    assert (Hstarf : star step init (t' ++ t) sf) by eauto using star_app.
    assert (Ho_sent : In o sf.(state.sent))
      by (rewrite (sent_eq_outputs (t' ++ t) sf Hstarf); exact Hino).
    pose proof (drive_to_dominate t s t' sf Hmrv Hstar Hallow Hrun Hinp) as Hdrive.
    apply eventually_will_step_annotate in Hdrive.
    unfold will_output_equiv.
    eapply eventually_trans; [exact Hdrive |].
    intros [s2 t2] (Hreach & Hle).
    destruct Hle as (_ & Hsent_dom).
    destruct (Hsent_dom o Ho_sent) as (o' & Ho'_in & Ho'_eq).
    destruct Hreach as (tr & Hstar_s_s2 & -> & Hga_imp).
    specialize (Hga_imp Hallow).
    assert (Hstar2 : star step init (tr ++ t) s2) by eauto using star_app.
    apply eventually_done.
    exists o'. split.
    - symmetry. exact Ho'_eq.
    - erewrite <- sent_eq_outputs by eassumption. eassumption.
  Qed.

  Lemma drive_to_dominate' t s s' t' :
    program.meta_rules_valid p ->
    star step init t s ->
    allowed_inputs (flat_map inputs_of t') ->
    star step init t' s' ->
    consistently_incl message.equiv claim consistent
      (flat_map inputs_of t) (flat_map inputs_of t') ->
    noncontradictory_wf message.equiv claim consistent allowed_inputs
      (flat_map inputs_of t) (flat_map inputs_of t') ->
    eventually will_step (fun '(s2, _) => nle s s2) (s', t').
  Proof.
    intros Hmrv Hstar Hga' Hstar' Hincl Hnc. revert Hincl Hnc.
    induction Hstar as [| Tp sm e s Hstar_T IH Hstep]; intros Hincl Hnc.
    - apply eventually_done. split.
      + apply consistently_incl_of_submultiset, submultiset_nil_l.
      + intros a Ha. destruct Ha.
    - cbn [inputs_of flat_map app] in Hincl, Hnc.
      destruct e as [m | lbl outs].
      + assert (HinclT : consistently_incl message.equiv claim consistent
                           (flat_map inputs_of Tp) (flat_map inputs_of t'))
          by (eapply consistently_incl_trans;
                [ apply consistently_incl_of_submultiset, submultiset_cons | exact Hincl ]).
        assert (HncT : noncontradictory_wf message.equiv claim consistent allowed_inputs
                         (flat_map inputs_of Tp) (flat_map inputs_of t'))
          by (eapply noncontradictory_wf_shrink_l; [ apply submultiset_cons | exact Hnc ]).
        specialize (IH HinclT HncT).
        apply eventually_will_step_annotate in IH.
        eapply eventually_weaken; [ exact IH | ].
        intros [s2 t2] (Hreach & Hle_sm).
        destruct Hreach as (tr & Hstar_s's2 & -> & _).
        invert Hstep.
        split.
        * cbn [state.known]. rewrite (known_eq_inputs Tp sm Hstar_T).
          eapply consistently_incl_trans; [ exact Hincl | ].
          apply consistently_incl_of_submultiset.
          eapply driven_inputs_submultiset; eassumption.
        * cbn [state.sent]. exact (proj2 Hle_sm).
      + specialize (IH Hincl Hnc).
        apply eventually_will_step_annotate in IH.
        eapply eventually_trans; [ exact IH | ].
        intros [s2 t2] (Hreach & Hle_sm).
        destruct Hreach as (tr & Hstar_s's2 & -> & Hga_imp).
        specialize (Hga_imp Hga').
        assert (Hstar2 : star step init (tr ++ t') s2) by eauto using star_app.
        eapply will_match; try eassumption.
        { eapply reachable_good; eassumption. }
        eapply knows_incl_grow with (l2 := s'.(state.known)).
        { eapply knows_incl_of_consistently_incl.
          { rewrite (known_eq_inputs Tp sm Hstar_T), (known_eq_inputs t' s' Hstar').
            exact Hincl. }
          { rewrite (known_eq_inputs Tp sm Hstar_T), (known_eq_inputs t' s' Hstar').
            exact Hnc. }
          rewrite (known_eq_inputs t' s' Hstar'). exact Hga'. }
        { exact (proj1 (step_star_mono s' tr s2 Hstar_s's2)). }
        rewrite (known_eq_inputs (tr ++ t') s2 Hstar2). exact Hga_imp.
  Qed.

  Lemma might_implies_will' :
    program.meta_rules_valid p ->
    might_implies_will_equiv' step message.equiv claim consistent allowed_inputs init.
  Proof.
    intros Hmrv t s o Hstar Hallow Hino s' t' Hnc Hincl Hstar' Hallow'.
    assert (Ho_sent : In o s.(state.sent))
      by (rewrite (sent_eq_outputs t s Hstar); exact Hino).
    pose proof (drive_to_dominate' t s s' t' Hmrv Hstar Hallow' Hstar' Hincl Hnc) as Hdrive.
    apply eventually_will_step_annotate in Hdrive.
    unfold will_output_equiv.
    eapply eventually_trans; [exact Hdrive |].
    intros [s2 t2] (Hreach & Hle).
    destruct Hle as (_ & Hsent_dom).
    destruct (Hsent_dom o Ho_sent) as (o' & Ho'_in & Ho'_eq).
    destruct Hreach as (tr & Hstar_s'_s2 & -> & Hga_imp).
    specialize (Hga_imp Hallow').
    assert (Hstar2 : star step init (tr ++ t') s2) by eauto using star_app.
    apply eventually_done.
    exists o'. split.
    - symmetry. exact Ho'_eq.
    - erewrite <- sent_eq_outputs by eassumption. eassumption.
  Qed.

End __.
End node.
