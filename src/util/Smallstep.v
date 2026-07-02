(*worth comparing to https://compcert.org/doc/html/compcert.common.Smallstep.html*)
From Stdlib Require Import List Permutation RelationClasses.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
Import ListNotations.

Section star.
  Context {state event : Type} (trace := list event)
          (step : state -> event -> state -> Prop).
  (* Traces are newest-first: the head is the most recent step.  This matches
     the IO layer, which writes a run [t'] in front of the history [t] as
     [t' ++ t]. *)
  Inductive star : state -> trace -> state -> Prop :=
  | star_refl s :
    star s [] s
  | star_step s t0 s' e s'' :
    star s t0 s' ->
    step s' e s'' ->
    star s (e :: t0) s''.

  Lemma star_one s e s' : step s e s' -> star s [e] s'.
  Proof. intros. eapply star_step; [apply star_refl | eassumption]. Qed.

  Lemma star_app s1 t1 s2 t2 s3 :
    star s1 t1 s2 -> star s2 t2 s3 -> star s1 (t2 ++ t1) s3.
  Proof.
    intros H1 H2. induction H2 as [ | s t0 s' e s'' Hstar IH Hstep]; cbn.
    - exact H1.
    - eapply star_step; [exact (IH H1) | exact Hstep].
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

  Definition consistent_monotone :=
    forall c l1 l2,
      allowed l1 ->
      allowed l2 ->
      submultiset l1 l2 ->
      consistent c l1 ->
      consistent c l2.

  Context (Hcm : consistent_monotone).

  Context (allowed_perm :
            forall l1 l2, Permutation l1 l2 -> allowed l1 -> allowed l2).

  Context (allowed_submultiset :
            forall l1 l2, submultiset l1 l2 -> allowed l2 -> allowed l1).

  Lemma submultiset_refl l : submultiset l l.
  Proof. exists []. rewrite app_nil_r. apply Permutation_refl. Qed.

  Lemma outputs_of_perm (t1 t2 : list (IO_event label message)) :
    Permutation t1 t2 -> Permutation (outputs_of t1) (outputs_of t2).
  Proof.
    unfold outputs_of. induction 1; cbn [flat_map].
    - apply Permutation_refl.
    - apply Permutation_app_head; assumption.
    - rewrite 2!app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
    - eapply perm_trans; eassumption.
  Qed.

  Lemma outputs_of_app (t1 t2 : list (IO_event label message)) :
    outputs_of (t1 ++ t2) = outputs_of t1 ++ outputs_of t2.
  Proof. apply flat_map_app. Qed.

  Lemma outputs_of_in_perm o (t1 t2 : list (IO_event label message)) :
    Permutation t1 t2 -> In o (outputs_of t1) -> In o (outputs_of t2).
  Proof.
    intros Hperm Hin. eapply Permutation_in; [apply outputs_of_perm; exact Hperm | exact Hin].
  Qed.

  Lemma inputs_of_perm (t1 t2 : list (IO_event label message)) :
    Permutation t1 t2 -> Permutation (inputs_of t1) (inputs_of t2).
  Proof.
    unfold inputs_of. induction 1; cbn [flat_map].
    - apply Permutation_refl.
    - apply Permutation_app_head; assumption.
    - rewrite 2!app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
    - eapply perm_trans; eassumption.
  Qed.

  Lemma inputs_of_app (t1 t2 : list (IO_event label message)) :
    inputs_of (t1 ++ t2) = inputs_of t1 ++ inputs_of t2.
  Proof. apply flat_map_app. Qed.

  Lemma outputs_of_in_app o (l1 l2 : list (IO_event label message)) :
    In o (outputs_of (l1 ++ l2)) <-> In o (outputs_of l1) \/ In o (outputs_of l2).
  Proof. rewrite outputs_of_app. apply in_app_iff. Qed.

  Lemma outputs_of_in_swap o l1 e (l2 : list (IO_event label message)) :
    In o (outputs_of (l1 ++ e :: l2)) <-> In o (outputs_of (e :: l1 ++ l2)).
  Proof.
    split.
    - apply outputs_of_in_perm. apply Permutation_sym. apply Permutation_middle.
    - apply outputs_of_in_perm. apply Permutation_middle.
  Qed.

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
    - destruct (IH s) as (tr & s_mid & Hstar & Hinp).
      destruct (Htotal s_mid m) as (s' & Hstep).
      exists (I_event m :: tr), s'. split.
      + eapply star_step; [exact Hstar | exact Hstep].
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
    - destruct (IH s) as (s_mid & Hstar).
      destruct (Htotal s_mid m) as (s' & Hstep).
      exists s'. cbn. eapply star_step; [exact Hstar | exact Hstep].
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
        P (s', tr ++ t).
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
        exists s_final, (tr ++ [O_event lbl outs]). split.
        * eapply star_app; [apply star_one; exact Hstep | exact Hstar].
        * split.
          -- rewrite inputs_of_app, Hinp. reflexivity.
          -- rewrite <- app_assoc. exact HP.
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
  Proof.
    intros s0 t0 o Hall Hwill.
    cbv [will_output] in Hwill.
    remember (s0, t0) as st eqn:Est.
    revert s0 t0 Hall Est.
    induction Hwill as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
      intros s0 t0 Hall [= -> ->].
    - exists [], s0. split; [constructor|].
      split; [reflexivity|exact HP].
    - cbv [will_step] in Hcan. destruct Hcan as [lbl Hcan].
      specialize (Hcan s0 [] (star_refl _ _)).
      cbn in Hcan. specialize (Hcan Hall).
      destruct Hcan as [Hmid0 | (s'' & outs & Hstep & Hmidset)].
      + apply (IH (s0, t0) Hmid0 s0 t0 Hall eq_refl).
      + assert (Hall' : allowed (inputs_of (O_event lbl outs :: t0))).
        { exact Hall. }
        destruct (IH _ Hmidset s'' (O_event lbl outs :: t0) Hall' eq_refl)
          as (t'' & s''' & Hstar'' & Hinp'' & Hout'').
        exists (t'' ++ [O_event lbl outs]), s'''. split.
        * eapply star_app; [apply star_one; exact Hstep | exact Hstar''].
        * split.
          -- rewrite inputs_of_app, Hinp''. reflexivity.
          -- rewrite <- app_assoc. exact Hout''.
  Qed.

  Lemma eventually_swap :
    forall (o : message) (s : state) (t1 t2 : list (IO_event label message)),
      Permutation t1 t2 ->
      eventually will_step
                 (fun '(_, t') => In o (outputs_of t')) (s, t1) ->
      eventually will_step
                 (fun '(_, t') => In o (outputs_of t')) (s, t2).
  Proof.
    intros o s t1 t2 Hperm Hev.
    remember (s, t1) as st eqn:Est.
    revert s t1 t2 Hperm Est.
    induction Hev as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
      intros s_orig t1 t2 Hperm [= -> ->].
    - apply eventually_done. cbn. eapply outputs_of_in_perm; eassumption.
    - destruct Hcan as [lbl Hcan].
      apply eventually_step_cps. exists lbl.
      intros s'_d t_d Hstar_d Hallow_d.
      assert (Hallow_d' : allowed (inputs_of (t_d ++ t1))).
      { eapply allowed_perm; [|exact Hallow_d].
        apply inputs_of_perm. apply Permutation_app_head. apply Permutation_sym. exact Hperm. }
      specialize (Hcan s'_d t_d Hstar_d Hallow_d').
      destruct Hcan as [Hmid_left | (s'' & outs & Hstep & Hmidset)].
      + left. apply (IH (s'_d, t_d ++ t1) Hmid_left s'_d (t_d ++ t1) (t_d ++ t2));
          [apply Permutation_app_head; exact Hperm | reflexivity].
      + right. exists s'', outs. split; [exact Hstep|].
        apply (IH _ Hmidset s'' (O_event lbl outs :: t_d ++ t1)
                  (O_event lbl outs :: t_d ++ t2));
          [apply perm_skip; apply Permutation_app_head; exact Hperm | reflexivity].
  Qed.

  Lemma will_output_step :
    forall s e s' t o,
      step s e s' ->
      will_output s t o ->
      will_output s' (e :: t) o.
  Proof.
    intros s e s' t o Hstep Hwill.
    cbv [will_output] in *.
    remember (s, t) as st eqn:Est.
    revert s e s' t Hstep Est.
    induction Hwill as [[s0 t0] HP | [s0 t0] midset Hcan Hmid IH];
      intros s_orig e_orig s_new t_orig Hstep [= -> ->].
    - apply eventually_done. cbn in HP |- *.
      apply in_or_app. right. exact HP.
    - destruct Hcan as [lbl Hcan].
      apply eventually_step_cps. exists lbl.
      intros s_d t_d Hstar_d Hallow_d.
      (* Fold the single step [e_orig] into the demon run [t_d]: with newest-first
         traces the combined run is [t_d ++ [e_orig]] and lands exactly where the
         demon does, so no permutation is needed. *)
      assert (Hstar_combined : star step s_orig (t_d ++ [e_orig]) s_d).
      { eapply star_app; [apply star_one; exact Hstep | exact Hstar_d]. }
      assert (Hallow_o : allowed (inputs_of ((t_d ++ [e_orig]) ++ t_orig))).
      { rewrite <- app_assoc. exact Hallow_d. }
      specialize (Hcan s_d (t_d ++ [e_orig]) Hstar_combined Hallow_o).
      destruct Hcan as [Hmid_left | (s'' & outs & Hstep_a & Hmidset)].
      + left. pose proof (Hmid _ Hmid_left) as Hev.
        rewrite <- app_assoc in Hev. exact Hev.
      + right. exists s'', outs. split; [exact Hstep_a|].
        pose proof (Hmid _ Hmidset) as Hev.
        rewrite <- app_assoc in Hev. exact Hev.
  Qed.
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
  Proof.
    intros Hciw ns tau e ns' o Halt Hstar Hstep Hcan.
    apply will_implies_might; [exact Halt|].
    apply (will_output_step ns e ns' tau o Hstep).
    apply Hciw; [exact Hstar | | exact Hcan].
    eapply allowed_submultiset; [|exact Halt].
    exists (inputs_of [e]). change (e :: tau) with ([e] ++ tau).
    rewrite inputs_of_app. apply Permutation_app_comm.
  Qed.

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
    - intros a Hincl Hcons. exists a. split; [|split].
      + destruct Hsub as (rest & Hperm). intros x Hx.
        eapply Permutation_in; [symmetry; exact Hperm|].
        apply in_or_app. left. apply Hincl. exact Hx.
      + clear Hincl Hcons. induction a as [|x xs IHa]; constructor; [reflexivity | exact IHa].
      + exact (Hcm a (inputs_of t1) (inputs_of t2) Hal1 Hal2 Hsub Hcons).
    - exact Hmight.
  Qed.

  Lemma ciw'_iff_ciw_and_monotone' :
    might_implies_will' <-> might_implies_will /\ monotone'.
  Proof.
    split.
    - (* → *)
      intros Hciw'. split.
      + (* can_implies_will *)
        intros t s o Hstar Hall Hcan.
        destruct Hcan as (T_a & s_f & Hstar_a & Hinp_a & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar Hstar_a) as Hstar_T.
        assert (HallT : allowed (inputs_of (T_a ++ t))).
        { rewrite inputs_of_app, Hinp_a. exact Hall. }
        apply (Hciw' (T_a ++ t) s_f o Hstar_T HallT Hout s t); auto.
        rewrite inputs_of_app, Hinp_a. apply incl_refl.
      + (* monotone' *)
        intros t1 t2 s1 s2 o Hstar1 Hstar2 Hall1 Hall2 Hincl Hcan1.
        destruct Hcan1 as (T_a & s_f & Hstar_a & Hinp_a & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar1 Hstar_a) as Hstar_T.
        assert (HallT : allowed (inputs_of (T_a ++ t1))).
        { rewrite inputs_of_app, Hinp_a. exact Hall1. }
        assert (HinclT : incl (inputs_of (T_a ++ t1)) (inputs_of t2)).
        { rewrite inputs_of_app, Hinp_a. exact Hincl. }
        pose proof (Hciw' (T_a ++ t1) s_f o Hstar_T HallT Hout s2 t2 HinclT Hstar2 Hall2)
          as Hwill.
        apply will_implies_might; assumption.
    - (* ← *)
      intros [Hciw Hmono] t s o Hstar Hall Hout s' t' Hincl Hstar' Hall'.
      apply Hciw; auto.
      apply (Hmono t t' s s' o Hstar Hstar' Hall Hall' Hincl).
      exists [], s. split; [constructor|]. split; [reflexivity|].
      cbn. exact Hout.
  Qed.

  Lemma ciw_monotone :
    might_implies_will ->
    monotone.
  Proof.
    cbv [might_implies_will monotone].
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
      + exact (will_implies_might _ _ _ Hallt (Hmid _ Hmid_left)).
      + specialize (Hmid _ Hmidset).
        assert (Hall' : allowed (inputs_of (O_event lbl outs :: t2 ++ t1))).
        { exact Hallt. }
        apply (will_implies_might _ _ _ Hall') in Hmid.
        destruct Hmid as (t' & s''' & Hstar' & Hinp' & Hout').
        exists (t' ++ [O_event lbl outs]), s'''. split.
        * eapply star_app; [apply star_one; exact Hstep | exact Hstar'].
        * split.
          -- rewrite inputs_of_app, Hinp'. reflexivity.
          -- rewrite <- app_assoc. exact Hout'.
  Qed.

  Definition ev_stable (P : state * list (IO_event label message) -> Prop) : Prop :=
    forall s s' e t,
      P (s, t) ->
      step s e s' ->
      P (s', e :: t).

  (* Lifting single-step stability over a whole run.  With newest-first traces
     the run [tau] lands directly in front of the history [t] as [tau ++ t] --
     no reversal, and hence no permutation needed. *)
  Lemma ev_stable_star :
    forall (P : state * list (IO_event label message) -> Prop),
      ev_stable P ->
      forall s tau s', star step s tau s' ->
        forall t, P (s, t) -> P (s', tau ++ t).
  Proof.
    intros P Hstable s tau s' Hstar. unfold ev_stable in Hstable.
    induction Hstar as [ | s0 t0 s1 e s2 Hstar' IH Hstep]; intros t HP.
    - exact HP.
    - cbn [app]. eapply Hstable; [apply IH; exact HP | exact Hstep].
  Qed.

  (* If [P] holds now and is stable, we may carry it through any [will_step]
     driving that establishes [Q]. *)
  Lemma eventually_carry_stable_gen :
    forall (P Q : state * list (IO_event label message) -> Prop),
      ev_stable P ->
      forall st,
        P st ->
        eventually will_step Q st ->
        eventually will_step (fun x => P x /\ Q x) st.
  Proof.
    intros P Q Hstable.
    intros st HP Hev. revert HP.
    induction Hev as [[s0 t0] HQ | [s0 t0] midset Hstep Hnext IH]; intros HP.
    - apply eventually_done. split; [exact HP | exact HQ].
    - destruct Hstep as [lbl Hstep].
      apply eventually_step_cps. exists lbl.
      intros s' td Hstar_d Hallow_d.
      (* P at the driven state [(s', td ++ t0)]: the demon run [td] lands directly
         in front of [t0], so single-step stability lifts over it with no perm. *)
      assert (HP' : P (s', td ++ t0)).
      { eapply ev_stable_star; [exact Hstable | exact Hstar_d | exact HP]. }
      specialize (Hstep s' td Hstar_d Hallow_d).
      destruct Hstep as [Hleft | (s'' & outs & Hst & Hright)].
      + left. apply (IH (s', td ++ t0) Hleft). exact HP'.
      + right. exists s'', outs. split; [exact Hst|].
        apply (IH (s'', O_event lbl outs :: td ++ t0) Hright).
        (* one more (single) step across the emitted output event *)
        eapply Hstable; [exact HP' | exact Hst].
  Qed.

  (* A [Q]-driving strategy from [(s,t)] can be advanced along any allowed run
     [star step s tau s'] to a strategy from [(s', tau ++ t)]. *)
  Lemma eventually_will_step_advance :
    forall (Q : state * list (IO_event label message) -> Prop),
      ev_stable Q ->
      forall s t s' tau,
        star step s tau s' ->
        allowed (inputs_of (tau ++ t)) ->
        eventually will_step Q (s, t) ->
        eventually will_step Q (s', tau ++ t).
  Proof.
    intros Q Hstable s t s' tau Hstar Hallow Hev.
    destruct Hev as [HQ | midset Hstep Hnext].
    - apply eventually_done.
      eapply ev_stable_star; [exact Hstable | exact Hstar | exact HQ].
    - destruct Hstep as [lblQ HQstep].
      apply eventually_step_cps. exists lblQ.
      intros s'' sigma Hstar_sigma Hallow_sigma.
      (* Fold [tau] into the demon's prefix: the combined run is [sigma ++ tau]
         (newest-first) and lands at [(sigma ++ tau) ++ t = sigma ++ (tau ++ t)],
         exactly the outer node -- so no permutation is needed. *)
      assert (Hcomb : star step s (sigma ++ tau) s'').
      { eapply star_app; [exact Hstar | exact Hstar_sigma]. }
      assert (Hallow_comb : allowed (inputs_of ((sigma ++ tau) ++ t))).
      { rewrite <- app_assoc. exact Hallow_sigma. }
      specialize (HQstep s'' (sigma ++ tau) Hcomb Hallow_comb).
      destruct HQstep as [Hleft | (s3 & outs & Hst & Hright)].
      + left. pose proof (Hnext _ Hleft) as Hev.
        rewrite <- app_assoc in Hev. exact Hev.
      + right. exists s3, outs. split; [exact Hst|].
        pose proof (Hnext _ Hright) as Hev.
        rewrite <- app_assoc in Hev. exact Hev.
  Qed.

  (* Binary intersection: [eventually will_step] is closed under conjunction of
     stable predicates.  No permutation-invariance needed: the steps producing
     [P] are folded into the demonic prefix of the [Q]-strategy. *)
  Lemma eventually_will_step_and :
    forall (P Q : state * list (IO_event label message) -> Prop),
      ev_stable P -> ev_stable Q ->
      forall st,
        eventually will_step P st ->
        eventually will_step Q st ->
        eventually will_step (fun x => P x /\ Q x) st.
  Proof.
    intros P Q HsP HsQ st HevP HevQ. revert HevQ.
    induction HevP as [[s0 t0] HP | [s0 t0] midset HstepP HnextP IHP]; intros HevQ.
    - apply eventually_carry_stable_gen; [exact HsP | exact HP | exact HevQ].
    - destruct HstepP as [lblP HstepP].
      apply eventually_step_cps. exists lblP.
      intros s' td Hstar_d Hallow_d.
      specialize (HstepP s' td Hstar_d Hallow_d).
      destruct HstepP as [Hleft | (s'' & outs & Hst & Hright)].
      + left. apply (IHP (s', td ++ t0) Hleft).
        eapply (eventually_will_step_advance Q HsQ s0 t0 s' td);
          [exact Hstar_d | exact Hallow_d | exact HevQ].
      + right. exists s'', outs. split; [exact Hst|].
        apply (IHP (s'', O_event lblP outs :: td ++ t0) Hright).
        eapply (eventually_will_step_advance Q HsQ s' (td ++ t0) s'' [O_event lblP outs]).
        * apply star_one; exact Hst.
        * exact Hallow_d.
        * eapply (eventually_will_step_advance Q HsQ s0 t0 s' td);
            [exact Hstar_d | exact Hallow_d | exact HevQ].
  Qed.

  Lemma ev_stable_Forall :
    forall {A} (F : A -> state * list (IO_event label message) -> Prop) (l : list A),
      (forall a, ev_stable (F a)) ->
      ev_stable (fun x => Forall (fun a => F a x) l).
  Proof.
    intros A F l HF. unfold ev_stable in *. intros s s' e t Hall Hstep.
    eapply Forall_impl; [| exact Hall]. intros x Hx. eapply HF; [exact Hx | exact Hstep].
  Qed.

  (* Finite intersection: closure under conjunction over a whole list. *)
  Lemma eventually_will_step_Forall :
    forall {A} (F : A -> state * list (IO_event label message) -> Prop) (l : list A) st,
      (forall a, ev_stable (F a)) ->
      Forall (fun a => eventually will_step (F a) st) l ->
      eventually will_step (fun x => Forall (fun a => F a x) l) st.
  Proof.
    intros A F l st HsF Hforall.
    induction l as [|a l IHl].
    - apply eventually_done. constructor.
    - pose proof (Forall_inv Hforall) as Hhead.
      pose proof (Forall_inv_tail Hforall) as Htail.
      specialize (IHl Htail).
      eapply eventually_weaken.
      + eapply (eventually_will_step_and
                  (F a) (fun x => Forall (fun a0 => F a0 x) l)).
        * exact (HsF a).
        * apply ev_stable_Forall. exact HsF.
        * exact Hhead.
        * exact IHl.
      + intros [s' t'] [H1 H2]. constructor; [exact H1 | exact H2].
  Qed.

  (* The originally-requested lemma is now a trivial corollary: each
     [might_output] gives, via [might_implies_will], an [eventually will_step]
     for that single output, all rooted at the same real start; intersect them. *)
  Lemma will_output_all :
    might_implies_will ->
    forall outs ns t,
      star step initial t ns ->
      allowed (inputs_of t) ->
      Forall (might_output ns t) outs ->
      eventually will_step
        (fun '(_, t') => Forall (fun o => In o (outputs_of t')) outs) (ns, t).
  Proof.
    intros Hmiw outs ns t Hstar Hallow HF.
    cbv [might_implies_will] in Hmiw.
    eapply eventually_weaken.
    - eapply (eventually_will_step_Forall
                (fun o => fun '(_, t') => In o (outputs_of t')) outs (ns, t)).
      + intros o s s' e t0 Hin Hstep.
        change (In o (outputs_of (e :: t0))).
        change (e :: t0) with ([e] ++ t0). rewrite outputs_of_app.
        apply in_or_app. right. exact Hin.
      + eapply Forall_impl; [| exact HF]. intros o Hmo.
        pose proof (Hmiw t ns o Hstar Hallow Hmo) as HW.
        cbv [will_output] in HW. exact HW.
    - intros [s' t'] H. exact H.
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
    might_implies_will ->
    complete.
  Proof.
    intros Hweak Hcan t s Hstar Hall o HD.
    apply Hcan; auto.
  Qed.
End step.

Section steps_corresp.
  Context {label message : Type}.
  Context (allowed : list message -> Prop).
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
        allowed (inputs_of t2) ->
        In output (outputs_of t2) ->
        produces step1 initial1 (inputs_of t2) output.

    Definition steps_corresp_sound' :=
      forall ns2 inps o,
        star step2 initial2 (map I_event inps) ns2 ->
        allowed inps ->
        will_output step2 allowed ns2 (map I_event inps) o ->
        produces step1 initial1 inps o.

    Definition steps_corresp_complete :=
      forall t2 ns2 output,
        star step2 initial2 t2 ns2 ->
        allowed (inputs_of t2) ->
        produces step1 initial1 (inputs_of t2) output ->
        might_output step2 ns2 t2 output.

    (* Primed completeness: restrict system 2's observed trace to be input-only
       (the dual restriction to steps_corresp_sound').  This is the form the
       cross-graph completeness lemma proves directly; the bridge below recovers
       the unprimed version from monotone'/input_total of system 2. *)
    Definition steps_corresp_complete' :=
      forall ns2 inps o,
        star step2 initial2 (map I_event inps) ns2 ->
        allowed inps ->
        produces step1 initial1 inps o ->
        might_output step2 ns2 (map I_event inps) o.

    Lemma complete_sound D :
      input_total step1 ->
      complete_weak step1 allowed initial1 D ->
      steps_corresp_complete ->
      complete_weak step2 allowed initial2 D.
    Proof.
      intros Hit1 Hcw1 Hcorresp t2 ns2 Hstar2 Hall2 o HD.
      destruct (star_recv step1 Hit1 (inputs_of t2) initial1)
        as (t1 & ns1 & Hstar1 & Hinp1).
      assert (Hall1 : allowed (inputs_of t1)).
      {  rewrite Hinp1. exact Hall2. }
      assert (HD1 : D (inputs_of t1) o) by (rewrite Hinp1; exact HD).
      apply (Hcw1 _ _ Hstar1 Hall1) in HD1.
      destruct HD1 as (t' & ns' & Hstar' & Hinpt' & Hout).
      pose proof (star_app _ _ _ _ _ _ Hstar1 Hstar') as Hstar_full.
      apply (Hcorresp t2 ns2 o Hstar2 Hall2).
      unfold produces. exists (t' ++ t1), ns'.
      split; [exact Hstar_full|]. split.
      - rewrite inputs_of_app, Hinpt'. exact Hinp1.
      - exact Hout.
    Qed.

    Lemma sound_sound D :
      sound step1 allowed initial1 D ->
      steps_corresp_sound ->
      sound step2 allowed initial2 D.
     Proof.
      intros Hs1 Hcorresp t2 s2 Hstar2 Hall2 o Hout2.
      pose proof (Hcorresp _ _ _ Hstar2 Hall2 Hout2) as Hpr. unfold produces in Hpr.
      destruct Hpr as (t1 & s1 & Hstar1 & Hinp & Hout1).
      assert (Hall1 : allowed (inputs_of t1)).
      {  rewrite Hinp. exact Hall2. }
      pose proof (Hs1 _ _ Hstar1 Hall1 _ Hout1) as HD.
      rewrite Hinp in HD. exact HD.
    Qed.

    Lemma steps_corresp_sound'_implies_sound :
      input_total step2 ->
      might_implies_will' step2 allowed initial2 ->
      steps_corresp_sound' ->
      steps_corresp_sound.
    Proof.
      intros Hit2 Hciw2 Hscs' t2 ns2 o Hstar2 Hall2 Hout2.
      destruct (star_recv_map step2 Hit2 (inputs_of t2) initial2) as (ns2' & Hstar2').
      assert (Hall' : allowed (inputs_of (map I_event (inputs_of t2) : list IO_event))).
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
      monotone' step2 allowed initial2 ->
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
        allowed (inputs_of t1) ->
        allowed (inputs_of t2) ->
        inputs_of t1 = inputs_of t2 ->
        forall output,
          might_output step1 ns1 t1 output <->
          might_output step2 ns2 t2 output.

    Lemma sound_complete_bicorresp :
      monotone' step1 allowed initial1 ->
      steps_corresp_complete ->
      steps_corresp_sound ->
      steps_bicorresp.
    Proof.
      intros Hmono Hcomp Hsound t1 t2 ns1 ns2 Hstar1 Hstar2 Hall1 Hall2 Heq o.
      split.
      - intros (t' & ns' & Hstar' & Hinpt' & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar1 Hstar') as Hstar1'.
        apply (Hcomp t2 ns2 o Hstar2 Hall2).
        unfold produces. exists (t' ++ t1), ns'.
        split; [exact Hstar1'|]. split.
        + rewrite inputs_of_app, Hinpt'. exact Heq.
        + exact Hout.
      - intros (t' & ns' & Hstar' & Hinpt' & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar2 Hstar') as Hstar2'.
        assert (Hall2' : allowed (inputs_of (t' ++ t2))).
        { rewrite inputs_of_app, Hinpt'. exact Hall2. }
        pose proof (Hsound _ _ _ Hstar2' Hall2' Hout) as Hpr. unfold produces in Hpr.
        destruct Hpr as (t1' & ns1' & Hstar1' & Heqinp & Hout1).
        assert (Hcan1' : might_output step1 ns1' t1' o).
        { exists [], ns1'. split; [constructor|].
          split; [reflexivity|exact Hout1]. }
        apply (Hmono t1' t1 ns1' ns1 o Hstar1' Hstar1); auto.
        + (* allowed (inputs_of t1') *)
           rewrite Heqinp. exact Hall2'.
        + (* incl *)
          rewrite Heqinp, inputs_of_app, Hinpt', <- Heq.
          apply incl_refl.
    Qed.

    Fail Fail Definition steps_equiv :=
      exists D,
        (*monotone D /\*)
        described_by step1 allowed initial1 D /\
          described_by step2 allowed initial2 D.
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
