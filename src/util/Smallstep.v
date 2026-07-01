(*worth comparing to https://compcert.org/doc/html/compcert.common.Smallstep.html*)
From Stdlib Require Import List Permutation RelationClasses.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
Import ListNotations.

Section star.
  Context {state event : Type} (trace := list event)
          (step : state -> event -> state -> Prop).
  Inductive star : state -> trace -> state -> Prop :=
  | star_refl s :
    star s [] s
  | star_step s e s' t0 s'' :
    step s e s' ->
    star s' t0 s'' ->
    star s (e :: t0) s''.

  Lemma star_app s1 t1 s2 t2 s3 :
    star s1 t1 s2 -> star s2 t2 s3 -> star s1 (t1 ++ t2) s3.
  Proof.
    induction 1; cbn; [auto|].
    econstructor; eauto.
  Qed.
End star.

Section io.
  Context {label message : Type}.

  Variant IO_event : Type :=
    | I_event : message -> IO_event
    | O_event : label -> list message -> IO_event.

  Definition inputs_of (t : list IO_event) :=
    flat_map (fun e => match e with I_event m => [m] | _ => [] end) t.

  Definition outputs_of (t : list IO_event) :=
    flat_map (fun e => match e with O_event _ outs => outs | _ => [] end) t.

  Lemma inputs_of_map_I_event (l : list message) :
    inputs_of (map I_event l) = l.
  Proof.
    unfold inputs_of.
    induction l as [|m l IH]; [reflexivity|].
    cbn. rewrite IH. reflexivity.
  Qed.
End io.

Arguments IO_event : clear implicits.

Section step.
  Context {state label message : Type}.
  Context (step : state -> IO_event label message -> state -> Prop).
  Context (equiv : message -> message -> Prop).
  Context (equiv_equiv : Equivalence equiv).
  Context (consistent : list message (*a set*) -> list message (*a multiset*) -> Prop).

  Definition submultiset (l1 l2 : list message) : Prop :=
    exists rest, Permutation l2 (l1 ++ rest).

  Context (allowed : list message -> Prop).

  Context (consistent_monotone :
            forall c l1 l2, allowed l1 ->
                       allowed l2 ->
                       submultiset l1 l2 ->
                       consistent c l1 ->
                       consistent c l2).

  Definition input_total :=
    forall s m, exists s', step s (I_event m) s'.

  Lemma star_recv :
    input_total ->
    forall (inputs : list message) (s : state),
      exists tr s', star step s tr s' /\ inputs_of tr = inputs.
  Proof.
    intros Htotal.
    induction inputs as [|m inputs IH]; intros s.
    - exists [], s. split; [constructor|reflexivity].
    - destruct (Htotal s m) as (s' & Hstep).
      destruct (IH s') as (tr & s'' & Hstar & Hinp).
      exists (I_event m :: tr), s''. split.
      + econstructor; eassumption.
      + cbn. f_equal. exact Hinp.
  Qed.

  Lemma star_recv_map :
    input_total ->
    forall (inputs : list message) (s : state),
      exists s', star step s (map I_event inputs) s'.
  Proof.
    intros Htotal.
    induction inputs as [|m inputs IH]; intros s.
    - exists s. constructor.
    - destruct (Htotal s m) as (s' & Hstep).
      destruct (IH s') as (s'' & Hstar).
      exists s''. cbn. econstructor; eassumption.
  Qed.

  (*some fairness condition: we can eventually take the step that we want.*)
  Definition will_step '(s, t) (P : state * list (IO_event label message) -> Prop) : Prop :=
    exists lbl,
    forall s' t',
      star step s t' s' ->
      allowed (inputs_of (t' ++ t)) ->
      P (s', t' ++ t) \/
        exists s'' outs,
          step s' (O_event lbl outs) s'' /\
            P (s'', O_event lbl outs :: t' ++ t).

  (*this is not used anywhere, but without it will_step is a bit weird, since it allows
    the good step to depend on the prior arbitrary sequence of steps.
    maybe we will want it later?*)
  Definition label_precise :=
    forall s lbl outs1 s1' outs2 s2',
      step s (O_event lbl outs1) s1' ->
      step s (O_event lbl outs2) s2' ->
      outs1 = outs2 /\ s1' = s2'.

  Lemma eventually_will_step_to_star :
    forall (P : state * list (IO_event label message) -> Prop) s t,
      allowed (inputs_of t) ->
      eventually will_step P (s, t) ->
      exists s' tr,
        star step s tr s' /\
        inputs_of tr = [] /\
        P (s', rev tr ++ t).
  Proof.
    intros P s0 t0 Hallow Hwill.
    remember (s0, t0) as st eqn:Est.
    revert s0 t0 Hallow Est.
    induction Hwill as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
      intros s0 t0 Hallow [= -> ->].
    - exists s0, []. split; [constructor|]. split; [reflexivity|exact HP].
    - destruct Hcan as [lbl Hcan].
      assert (Hallow0 : allowed (inputs_of ([] ++ t0))) by (cbn; exact Hallow).
      destruct (Hcan s0 [] (star_refl _ _) Hallow0)
        as [Hmid0 | (s'' & outs & Hstep & Hmidset)].
      + apply (IH (s0, [] ++ t0) Hmid0 s0 t0 Hallow eq_refl).
      + assert (Hallow' : allowed (inputs_of (O_event lbl outs :: t0))).
        { exact Hallow. }
        destruct (IH _ Hmidset s'' (O_event lbl outs :: t0) Hallow' eq_refl)
          as (s_final & tr & Hstar & Hinp & HP).
        exists s_final, (O_event lbl outs :: tr).
        split; [econstructor; eassumption|].
        split; [cbn; exact Hinp|].
        cbn. rewrite <- app_assoc. cbn. exact HP.
  Qed.

  Definition might_output start t output :=
    exists t' s',
      star step start t' s' /\
        inputs_of t' = [] /\
        In output (outputs_of (t' ++ t)).

  Definition might_output_equiv start t o :=
    exists o', equiv o' o /\ might_output start t o'.

  Definition produces (init : state) (inputs : list message) (output : message) : Prop :=
    exists t ns,
      star step init t ns /\
      inputs_of t = inputs /\
      In output (outputs_of t).

  Definition will_output start t (output : message) : Prop :=
    eventually will_step
      (fun '(_, t') => In output (outputs_of t'))
      (start, t).

  Definition will_output_equiv start t (output : message) : Prop :=
    eventually will_step
      (fun '(_, t') => exists o', equiv o' output /\ In o' (outputs_of t'))
      (start, t).

  Lemma will_implies_might :
    forall s t o,
      allowed (inputs_of t) ->
      will_output s t o ->
      might_output s t o.
  Proof. Admitted.

  Lemma will_output_step :
    forall s e s' t o,
      step s e s' ->
      will_output s t o ->
      will_output s' (e :: t) o.
  Proof. Admitted.
  Context (outputs_wf : list message -> Prop).
  Context (initial : state).

  Definition outputs_well_formed :=
    forall t s, star step initial t s -> outputs_wf (outputs_of t).

  Definition might_implies_will :=
    forall t s o,
      star step initial t s ->
      allowed (inputs_of t) ->
      might_output s t o ->
      will_output s t o.

  Definition might_implies_will_equiv :=
    forall t s o,
      star step initial t s ->
      allowed (inputs_of t) ->
      might_output s t o ->
      will_output_equiv s t o.

  Definition might_implies_will' :=
    forall t s o,
      star step initial t s ->
      allowed (inputs_of t) ->
      In o (outputs_of t) ->
      forall s' t',
        incl (inputs_of t) (inputs_of t') ->
        star step initial t' s' ->
        allowed (inputs_of t') ->
        will_output s' t' o.

  Lemma might_output_step_preserved :
    might_implies_will ->
    forall ns tau e ns' o,
      allowed (inputs_of (e :: tau)) ->
      star step initial tau ns ->
      step ns e ns' ->
      might_output ns tau o ->
      might_output ns' (e :: tau) o.
  Proof. Admitted.

  Definition monotone :=
    forall t1 t2 s1 s2 o,
      star step initial t1 s1 ->
      star step s1 t2 s2 ->
      allowed (inputs_of t1) ->
      allowed (inputs_of (t2 ++ t1)) ->
      might_output s1 t1 o ->
      might_output s2 (t2 ++ t1) o.

  Definition monotone' :=
    forall t1 t2 s1 s2 o,
      star step initial t1 s1 ->
      star step initial t2 s2 ->
      allowed (inputs_of t1) ->
      allowed (inputs_of t2) ->
      incl (inputs_of t1) (inputs_of t2) ->
      might_output s1 t1 o ->
      might_output s2 t2 o.

  Definition incl_mod (l1 l2 : list message) : Prop :=
    forall a,
      incl a l1 ->
      consistent a l1 ->
      exists b,
        incl b l2 /\ Forall2 equiv a b /\ consistent b l2.

  Definition monotone_mod_equiv :=
    forall t1 t2 s1 s2 o,
      star step initial t1 s1 ->
      star step initial t2 s2 ->
      allowed (inputs_of t1) ->
      allowed (inputs_of t2) ->
      incl_mod (inputs_of t1) (inputs_of t2) ->
      might_output s1 t1 o ->
      might_output_equiv s2 t2 o.

  Definition monotone_multiset :=
    forall t1 t2 s1 s2 o,
      star step initial t1 s1 ->
      star step initial t2 s2 ->
      allowed (inputs_of t1) ->
      allowed (inputs_of t2) ->
      submultiset (inputs_of t1) (inputs_of t2) ->
      might_output s1 t1 o ->
      might_output_equiv s2 t2 o.

  Lemma monotone_multiset_of_mod_equiv : monotone_mod_equiv -> monotone_multiset.
  Proof.
    intros Hmono t1 t2 s1 s2 o Hs1 Hs2 Hal1 Hal2 Hsub Hmight.
    apply (Hmono t1 t2 s1 s2 o Hs1 Hs2 Hal1 Hal2).
    - intros a Ha. exists a. split;
        [ destruct Hsub as (rest & Hperm); eapply Permutation_in;
            [symmetry; exact Hperm | apply in_or_app; left; exact Ha]
        | reflexivity ].
    - intros c Hwf. exact (well_formed_monotone c (inputs_of t1) (inputs_of t2) Hal1 Hal2 Hsub Hwf).
    - exact Hmight.
  Qed.

  Lemma ciw'_iff_ciw_and_monotone' :
    can_implies_will' <-> can_implies_will /\ monotone'.
  Proof.
    split.
    - (* → *)
      intros Hciw'. split.
      + (* can_implies_will *)
        intros t s o Hstar Hall Hcan.
        destruct Hcan as (T_a & s_f & Hstar_a & Hinp_a & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar Hstar_a) as Hstar_T.
        set (T := t ++ T_a) in *.
        assert (HallT : allowed (inputs_of T)).
        { subst T.
          rewrite inputs_of_app, Hinp_a, app_nil_r. exact Hall. }
        assert (HoutT : In o (outputs_of T)).
        { subst T. apply outputs_of_in_app.
          apply outputs_of_in_app in Hout as [Hout|Hout]; [right|left]; exact Hout. }
        apply (Hciw' T s_f o Hstar_T HallT HoutT s t); auto.
        subst T. rewrite inputs_of_app, Hinp_a, app_nil_r.
        apply incl_refl.
      + (* monotone' *)
        intros t1 t2 s1 s2 o Hstar1 Hstar2 Hall1 Hall2 Hincl Hcan1.
        destruct Hcan1 as (T_a & s_f & Hstar_a & Hinp_a & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar1 Hstar_a) as Hstar_T.
        set (T := t1 ++ T_a) in *.
        assert (HallT : allowed (inputs_of T)).
        { subst T.
          rewrite inputs_of_app, Hinp_a, app_nil_r. exact Hall1. }
        assert (HoutT : In o (outputs_of T)).
        { subst T. apply outputs_of_in_app.
          apply outputs_of_in_app in Hout as [Hout|Hout]; [right|left]; exact Hout. }
        assert (HinclT : incl (inputs_of T) (inputs_of t2)).
        { subst T. rewrite inputs_of_app, Hinp_a, app_nil_r. exact Hincl. }
        pose proof (Hciw' T s_f o Hstar_T HallT HoutT s2 t2 HinclT Hstar2 Hall2)
          as Hwill.
        apply will_implies_can; assumption.
    - (* ← *)
      intros [Hciw Hmono] t s o Hstar Hall Hout s' t' Hincl Hstar' Hall'.
      apply Hciw; auto.
      apply (Hmono t t' s s' o Hstar Hstar' Hall Hall' Hincl).
      exists [], s. split; [constructor|]. split; [reflexivity|].
      cbn. exact Hout.
  Qed.

  Lemma ciw_monotone :
    can_implies_will ->
    monotone.
  Proof.
    cbv [can_implies_will monotone].
    intros Hciw t1 t2 s1 s2 o Hstar1 Hstar2 Hall1 Hallt Hcan.
    apply (Hciw _ _ _ Hstar1 Hall1) in Hcan.
    cbv [will_output] in Hcan.
    inversion Hcan as [HP | midset Hwill_step Hmid]; clear Hcan; subst.
    - exists [], s2. split; [constructor|].
      split; [reflexivity|].
      cbn. apply outputs_of_in_app. right. exact HP.
    - cbv [will_step] in Hwill_step. destruct Hwill_step as [lbl Hwill_step].
      specialize (Hwill_step _ _ Hstar2 Hallt).
      destruct Hwill_step as [Hmid_left | (s'' & outs & Hstep & Hmidset)].
      + exact (will_implies_can _ _ _ Hallt (Hmid _ Hmid_left)).
      + specialize (Hmid _ Hmidset).
        assert (Hall' : allowed (inputs_of (O_event lbl outs :: t2 ++ t1))).
        { exact Hallt. }
        apply (will_implies_can _ _ _ Hall') in Hmid.
        destruct Hmid as (t' & s''' & Hstar' & Hinp' & Hout').
        exists (O_event lbl outs :: t'), s'''.
        split; [econstructor; eassumption|].
        split; [cbn; exact Hinp'|].
        apply (outputs_of_in_swap o t' (O_event lbl outs) (t2 ++ t1)). exact Hout'.
  Qed.

  Context (D : list message -> message -> Prop).

  Definition complete :=
    forall t s,
      star step initial t s ->
      allowed (inputs_of t) ->
      forall output,
        D (inputs_of t) output ->
        will_output s t output.

  Definition sound :=
    forall t s,
      star step initial t s ->
      allowed (inputs_of t) ->
      forall output,
        In output (outputs_of t) ->
        D (inputs_of t) output.

  Definition described_by := sound /\ complete.

  Definition complete_weak :=
    forall t s,
      star step initial t s ->
      allowed (inputs_of t) ->
      forall output,
        D (inputs_of t) output ->
        might_output s t output.

  Definition described_by_weak := sound /\ complete_weak.

  Lemma complete_weak_implies_strong :
    complete_weak ->
    can_implies_will ->
    complete.
  Proof.
    intros Hweak Hcan t s Hstar Hall o HD.
    apply Hcan; auto.
  Qed.
End step.

Section steps_corresp.
  Context {label message : Type}.
  Context (well_formed : message -> list message -> Prop).
  Local Notation IO_event := (IO_event label message).

  Section steps.
    Context {state1 : Type}.
    Context (step1 : state1 -> IO_event -> state1 -> Prop).
    Context (initial1 : state1).

    Context {state2 : Type}.
    Context (step2 : state2 -> IO_event -> state2 -> Prop).
    Context (initial2 : state2).

    Definition steps_corresp_sound :=
      forall t2 ns2 output,
        star step2 initial2 t2 ns2 ->
        allowed well_formed (inputs_of t2) ->
        In output (outputs_of t2) ->
        produces step1 initial1 (inputs_of t2) output.

    Definition steps_corresp_sound' :=
      forall ns2 inps o,
        star step2 initial2 (map I_event inps) ns2 ->
        allowed well_formed inps ->
        will_output step2 well_formed ns2 (map I_event inps) o ->
        produces step1 initial1 inps o.

    Definition steps_corresp_complete :=
      forall t2 ns2 output,
        star step2 initial2 t2 ns2 ->
        allowed well_formed (inputs_of t2) ->
        produces step1 initial1 (inputs_of t2) output ->
        might_output step2 ns2 t2 output.

    (* Primed completeness: restrict system 2's observed trace to be input-only
       (the dual restriction to steps_corresp_sound').  This is the form the
       cross-graph completeness lemma proves directly; the bridge below recovers
       the unprimed version from monotone'/input_total of system 2. *)
    Definition steps_corresp_complete' :=
      forall ns2 inps o,
        star step2 initial2 (map I_event inps) ns2 ->
        allowed well_formed inps ->
        produces step1 initial1 inps o ->
        might_output step2 ns2 (map I_event inps) o.

    Lemma complete_sound D :
      input_total step1 ->
      complete_weak step1 well_formed initial1 D ->
      steps_corresp_complete ->
      complete_weak step2 well_formed initial2 D.
    Proof.
      intros Hit1 Hcw1 Hcorresp t2 ns2 Hstar2 Hall2 o HD.
      destruct (star_recv step1 Hit1 (inputs_of t2) initial1)
        as (t1 & ns1 & Hstar1 & Hinp1).
      assert (Hall1 : allowed well_formed (inputs_of t1)).
      {  rewrite Hinp1. exact Hall2. }
      assert (HD1 : D (inputs_of t1) o) by (rewrite Hinp1; exact HD).
      apply (Hcw1 _ _ Hstar1 Hall1) in HD1.
      destruct HD1 as (t' & ns' & Hstar' & Hinpt' & Hout).
      pose proof (star_app _ _ _ _ _ _ Hstar1 Hstar') as Hstar_full.
      apply (Hcorresp t2 ns2 o Hstar2 Hall2).
      unfold produces. exists (t1 ++ t'), ns'.
      split; [exact Hstar_full|]. split.
      - rewrite inputs_of_app, Hinpt', app_nil_r. exact Hinp1.
      - apply outputs_of_in_app. apply outputs_of_in_app in Hout.
        destruct Hout as [Hout|Hout]; [right|left]; exact Hout.
    Qed.

    Lemma sound_sound D :
      sound step1 well_formed initial1 D ->
      steps_corresp_sound ->
      sound step2 well_formed initial2 D.
     Proof.
      intros Hs1 Hcorresp t2 s2 Hstar2 Hall2 o Hout2.
      pose proof (Hcorresp _ _ _ Hstar2 Hall2 Hout2) as Hpr. unfold produces in Hpr.
      destruct Hpr as (t1 & s1 & Hstar1 & Hinp & Hout1).
      assert (Hall1 : allowed well_formed (inputs_of t1)).
      {  rewrite Hinp. exact Hall2. }
      pose proof (Hs1 _ _ Hstar1 Hall1 _ Hout1) as HD.
      rewrite Hinp in HD. exact HD.
    Qed.

    Lemma steps_corresp_sound'_implies_sound :
      input_total step2 ->
      can_implies_will' step2 well_formed initial2 ->
      steps_corresp_sound' ->
      steps_corresp_sound.
    Proof.
      intros Hit2 Hciw2 Hscs' t2 ns2 o Hstar2 Hall2 Hout2.
      destruct (star_recv_map step2 Hit2 (inputs_of t2) initial2) as (ns2' & Hstar2').
      assert (Hall' : allowed well_formed (inputs_of (map I_event (inputs_of t2) : list IO_event))).
      {  rewrite inputs_of_map_I_event. exact Hall2. }
      assert (Hincl : incl (inputs_of t2)
                           (inputs_of (map I_event (inputs_of t2) : list IO_event))).
      { rewrite inputs_of_map_I_event. apply incl_refl. }
      pose proof (Hciw2 t2 ns2 o Hstar2 Hall2 Hout2
                       ns2' (map I_event (inputs_of t2)) Hincl Hstar2' Hall') as Hwill.
      exact (Hscs' ns2' (inputs_of t2) o Hstar2' Hall2 Hwill).
    Qed.

    (* Dual bridge: recover unprimed completeness from the primed version, using
       input_total (to realize the input-only run) and monotone' (to transfer the
       capability to the actually-observed run on the same inputs). *)
    Lemma steps_corresp_complete'_implies_complete :
      input_total step2 ->
      monotone' step2 well_formed initial2 ->
      steps_corresp_complete' ->
      steps_corresp_complete.
    Proof.
      intros Hit2 Hmono2 Hcc' t2 ns2 o Hstar2 Hall2 Hprod.
      destruct (star_recv_map step2 Hit2 (inputs_of t2) initial2) as (ns2' & Hstar2').
      pose proof (Hcc' ns2' (inputs_of t2) o Hstar2' Hall2 Hprod) as Hcan'.
      apply (Hmono2 (map I_event (inputs_of t2)) t2 ns2' ns2 o Hstar2' Hstar2).
      -  rewrite inputs_of_map_I_event. exact Hall2.
      - exact Hall2.
      - rewrite inputs_of_map_I_event. apply incl_refl.
      - exact Hcan'.
    Qed.

    Definition steps_bicorresp :=
      forall t1 t2 ns1 ns2,
        star step1 initial1 t1 ns1 ->
        star step2 initial2 t2 ns2 ->
        allowed well_formed (inputs_of t1) ->
        allowed well_formed (inputs_of t2) ->
        inputs_of t1 = inputs_of t2 ->
        forall output,
          might_output step1 ns1 t1 output <->
          might_output step2 ns2 t2 output.

    Lemma sound_complete_bicorresp :
      monotone' step1 well_formed initial1 ->
      steps_corresp_complete ->
      steps_corresp_sound ->
      steps_bicorresp.
    Proof.
      intros Hmono Hcomp Hsound t1 t2 ns1 ns2 Hstar1 Hstar2 Hall1 Hall2 Heq o.
      split.
      - intros (t' & ns' & Hstar' & Hinpt' & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar1 Hstar') as Hstar1'.
        apply (Hcomp t2 ns2 o Hstar2 Hall2).
        unfold produces. exists (t1 ++ t'), ns'.
        split; [exact Hstar1'|]. split.
        + rewrite inputs_of_app, Hinpt', app_nil_r. exact Heq.
        + apply outputs_of_in_app. apply outputs_of_in_app in Hout.
          destruct Hout as [Hout|Hout]; [right|left]; exact Hout.
      - intros (t' & ns' & Hstar' & Hinpt' & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar2 Hstar') as Hstar2'.
        assert (Hall2' : allowed well_formed (inputs_of (t2 ++ t'))).
        {
          rewrite inputs_of_app, Hinpt', app_nil_r. exact Hall2. }
        assert (Hout2' : In o (outputs_of (t2 ++ t'))).
        { apply outputs_of_in_app. apply outputs_of_in_app in Hout.
          destruct Hout as [Hout|Hout]; [right|left]; exact Hout. }
        pose proof (Hsound _ _ _ Hstar2' Hall2' Hout2') as Hpr. unfold produces in Hpr.
        destruct Hpr as (t1' & ns1' & Hstar1' & Heqinp & Hout1).
        assert (Hcan1' : might_output step1 ns1' t1' o).
        { exists [], ns1'. split; [constructor|].
          split; [reflexivity|exact Hout1]. }
        apply (Hmono t1' t1 ns1' ns1 o Hstar1' Hstar1); auto.
        + (* allowed (inputs_of t1') *)
           rewrite Heqinp. exact Hall2'.
        + (* incl *)
          rewrite Heqinp, inputs_of_app, Hinpt', app_nil_r, <- Heq.
          apply incl_refl.
    Qed.

    Fail Fail Definition steps_equiv :=
      exists D,
        (*monotone D /\*)
        described_by step1 well_formed initial1 D /\
          described_by step2 well_formed initial2 D.
  End steps.

  Section steps.
    Context {state1 : Type}.
    Context (step1 : state1 -> IO_event -> state1 -> Prop).
    Context (initial1 : state1).

    Context {state2 : Type}.
    Context (step2 : state2 -> IO_event -> state2 -> Prop).
    Context (initial2 : state2).

    Lemma sound_impl_complete :
      steps_corresp_sound step1 initial1 step2 initial2 ->
      steps_corresp_complete step2 initial2 step1 initial1.
    Proof. Abort.

    Lemma complete_impl_sound :
      steps_corresp_complete step2 initial2 step1 initial1 ->
      steps_corresp_sound step1 initial1 step2 initial2.
    Proof. Abort.
  End steps.
End steps_corresp.
