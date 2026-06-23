(*worth comparing to https://compcert.org/doc/html/compcert.common.Smallstep.html*)
From Stdlib Require Import List.
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
  Context {message : Type}.

  Variant IO_event : Type :=
    | I_event : message -> IO_event
    | O_event : list message -> IO_event.

  Definition inputs_of (t : list IO_event) :=
    flat_map (fun e => match e with I_event m => [m] | _ => [] end) t.

  Definition output_in_trace (output : message) (t : list IO_event) :=
    exists outs, In (O_event outs) t /\ In output outs.

  Lemma inputs_of_map_I_event (l : list message) :
    inputs_of (map I_event l) = l.
  Proof.
    unfold inputs_of.
    induction l as [|m l IH]; [reflexivity|].
    cbn. rewrite IH. reflexivity.
  Qed.
End io.

Arguments IO_event : clear implicits.

Section __.
  Context {state message : Type}.
  Context (step : state -> IO_event message -> state -> Prop).
  Context (allowed : list message -> Prop).

  Definition allowed_trace (t : list (IO_event message)) := allowed (inputs_of t).

  Lemma output_in_trace_app o (l1 l2 : list (IO_event message)) :
    output_in_trace o (l1 ++ l2) <-> output_in_trace o l1 \/ output_in_trace o l2.
  Proof.
    unfold output_in_trace; split.
    - intros (outs & Hin & Hino).
      apply in_app_or in Hin as [Hin|Hin]; [left|right]; eauto.
    - intros [(outs & Hin & Hino)|(outs & Hin & Hino)];
        exists outs; (split; [apply in_or_app|exact Hino]); auto.
  Qed.

  Lemma output_in_trace_rev o (l : list (IO_event message)) :
    output_in_trace o (rev l) <-> output_in_trace o l.
  Proof.
    unfold output_in_trace; split; intros (outs & Hin & Hino); exists outs;
      (split; [|exact Hino]); apply in_rev; auto.
    rewrite rev_involutive. exact Hin.
  Qed.

  Lemma allowed_trace_universal :
    (forall t, allowed t) -> forall t, allowed_trace t.
  Proof. unfold allowed_trace; auto. Qed.

  Lemma inputs_of_app (t1 t2 : list (IO_event message)) :
    inputs_of (t1 ++ t2) = inputs_of t1 ++ inputs_of t2.
  Proof. apply flat_map_app. Qed.

  Lemma output_in_trace_swap o l1 e (l2 : list (IO_event message)) :
    output_in_trace o (l1 ++ e :: l2) <-> output_in_trace o (e :: l1 ++ l2).
  Proof.
    unfold output_in_trace.
    split; intros (outs & Hin & Hino); exists outs; (split; [|exact Hino]).
    - apply in_app_or in Hin. destruct Hin as [Hin | [Hin | Hin]].
      + right. apply in_or_app. left. exact Hin.
      + left. exact Hin.
      + right. apply in_or_app. right. exact Hin.
    - destruct Hin as [Hin | Hin].
      + apply in_or_app. right. left. exact Hin.
      + apply in_app_or in Hin. destruct Hin as [Hin | Hin].
        * apply in_or_app. left. exact Hin.
        * apply in_or_app. right. right. exact Hin.
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
    - destruct (Htotal s m) as (s' & Hstep).
      destruct (IH s') as (tr & s'' & Hstar & Hinp).
      exists (I_event m :: tr), s''. split.
      + econstructor; eassumption.
      + cbn. f_equal. exact Hinp.
  Qed.

  (*some fairness condition: we can eventually take the step that we want.
    i wonder whether (exists outs) should appear before (forall s' t')?
    probably not.
   *)
  Definition can_step '(s, t) (P : state * list (IO_event message) -> Prop) : Prop :=
    forall s' t',
      star step s t' s' ->
      allowed_trace (t' ++ t) ->
      P (s', t' ++ t) \/
        exists s'' outs,
          step s' (O_event outs) s'' /\
            P (s'', O_event outs :: t' ++ t).

  Lemma eventually_can_step_to_star :
    forall (P : state * list (IO_event message) -> Prop) s t,
      allowed_trace t ->
      eventually can_step P (s, t) ->
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
    - assert (Hallow0 : allowed_trace ([] ++ t0)) by (cbn; exact Hallow).
      destruct (Hcan s0 [] (star_refl _ _) Hallow0)
        as [Hmid0 | (s'' & outs & Hstep & Hmidset)].
      + apply (IH (s0, [] ++ t0) Hmid0 s0 t0 Hallow eq_refl).
      + assert (Hallow' : allowed_trace (O_event outs :: t0)).
        { unfold allowed_trace. cbn. exact Hallow. }
        destruct (IH _ Hmidset s'' (O_event outs :: t0) Hallow' eq_refl)
          as (s_final & tr & Hstar & Hinp & HP).
        exists s_final, (O_event outs :: tr).
        split; [econstructor; eassumption|].
        split; [cbn; exact Hinp|].
        cbn. rewrite <- app_assoc. cbn. exact HP.
  Qed.

  Definition can_output start t output :=
    exists t' s',
      star step start t' s' /\
        inputs_of t' = [] /\
        output_in_trace output (t' ++ t).

  Definition will_output start t (output : message) : Prop :=
    eventually can_step
      (fun '(_, t') => output_in_trace output t')
      (start, t).

  Lemma will_implies_can :
    forall s t o,
      allowed_trace t ->
      will_output s t o ->
      can_output s t o.
  Proof.
    intros s0 t0 o Hall Hwill.
    cbv [will_output] in Hwill.
    remember (s0, t0) as st eqn:Est.
    revert s0 t0 Hall Est.
    induction Hwill as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
      intros s0 t0 Hall [= -> ->].
    - exists [], s0. split; [constructor|].
      split; [reflexivity|exact HP].
    - cbv [can_step] in Hcan.
      specialize (Hcan s0 [] (star_refl _ _)).
      cbn in Hcan. specialize (Hcan Hall).
      destruct Hcan as [Hmid0 | (s'' & outs & Hstep & Hmidset)].
      + apply (IH (s0, t0) Hmid0 s0 t0 Hall eq_refl).
      + assert (Hall' : allowed_trace (O_event outs :: t0)).
        { unfold allowed_trace. cbn. exact Hall. }
        destruct (IH _ Hmidset s'' (O_event outs :: t0) Hall' eq_refl)
          as (t'' & s''' & Hstar'' & Hinp'' & Hout'').
        exists (O_event outs :: t''), s'''.
        split; [econstructor; eassumption|].
        split; [cbn; exact Hinp''|].
        cbn. apply output_in_trace_swap. exact Hout''.
  Qed.

  Lemma eventually_swap :
    (forall t, allowed t) ->
    forall (o : message) (s : state) (t1 t2 : list (IO_event message)),
      (forall x, output_in_trace x t1 <-> output_in_trace x t2) ->
      eventually can_step
                 (fun '(_, t') => output_in_trace o t') (s, t1) ->
      eventually can_step
                 (fun '(_, t') => output_in_trace o t') (s, t2).
  Proof.
    intros A_univ o s t1 t2 Hout Hev.
    remember (s, t1) as st eqn:Est.
    revert s t1 t2 Hout Est.
    induction Hev as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
      intros s_orig t1 t2 Hout [= -> ->].
    - apply eventually_done. cbn. apply Hout. exact HP.
    - apply eventually_step_cps.
      intros s'_d t_d Hstar_d Hallow_d.
      assert (Hallow_d' : allowed_trace (t_d ++ t1))
        by (unfold allowed_trace; auto).
      specialize (Hcan s'_d t_d Hstar_d Hallow_d').
      destruct Hcan as [Hmid_left | (s'' & outs & Hstep & Hmidset)].
      + left. apply (IH (s'_d, t_d ++ t1) Hmid_left s'_d (t_d ++ t1) (t_d ++ t2));
          [|reflexivity].
        intros x. rewrite !output_in_trace_app. pose proof (Hout x). tauto.
      + right. exists s'', outs. split; [exact Hstep|].
        apply (IH _ Hmidset s'' (O_event outs :: t_d ++ t1)
                  (O_event outs :: t_d ++ t2)); [|reflexivity].
        intros x.
        change (O_event outs :: t_d ++ t1) with ([O_event outs] ++ (t_d ++ t1)).
        change (O_event outs :: t_d ++ t2) with ([O_event outs] ++ (t_d ++ t2)).
        rewrite !output_in_trace_app.
        pose proof (output_in_trace_app x t_d t1) as Ht1.
        pose proof (output_in_trace_app x t_d t2) as Ht2.
        pose proof (Hout x). tauto.
  Qed.

  Lemma will_output_step :
    (forall t, allowed t) ->
    forall s e s' t o,
      step s e s' ->
      will_output s t o ->
      will_output s' (e :: t) o.
  Proof.
    intros A_univ s e s' t o Hstep Hwill.
    cbv [will_output] in *.
    remember (s, t) as st eqn:Est.
    revert s e s' t Hstep Est.
    induction Hwill as [[s0 t0] HP | [s0 t0] midset Hcan Hmid IH];
      intros s_orig e_orig s_new t_orig Hstep [= -> ->].
    - apply eventually_done. cbn in HP |- *.
      destruct HP as (outs & Hin & Hino).
      exists outs. split; [right; exact Hin | exact Hino].
    - apply eventually_step_cps.
      intros s_d t_d Hstar_d Hallow_d.
      pose proof (star_step _ _ _ _ _ _ Hstep Hstar_d) as Hstar_combined.
      assert (Hallow_o : allowed_trace ((e_orig :: t_d) ++ t_orig))
        by (unfold allowed_trace; auto).
      specialize (Hcan s_d (e_orig :: t_d) Hstar_combined Hallow_o).
      destruct Hcan as [Hmid_left | (s'' & outs & Hstep_a & Hmidset)].
      + left.
        apply (eventually_swap A_univ o s_d
                ((e_orig :: t_d) ++ t_orig)
                (t_d ++ e_orig :: t_orig)); [|apply (Hmid _ Hmid_left)].
        intros x.
        change ((e_orig :: t_d) ++ t_orig) with (e_orig :: t_d ++ t_orig).
        pose proof (output_in_trace_swap x t_d e_orig t_orig) as Hsw.
        tauto.
      + right. exists s'', outs. split; [exact Hstep_a|].
        specialize (Hmid _ Hmidset).
        apply (eventually_swap A_univ o s''
                (O_event outs :: (e_orig :: t_d) ++ t_orig)
                (O_event outs :: t_d ++ e_orig :: t_orig)); [|exact Hmid].
        intros x.
        change ((e_orig :: t_d) ++ t_orig) with (e_orig :: t_d ++ t_orig).
        change (O_event outs :: e_orig :: t_d ++ t_orig)
          with ([O_event outs] ++ (e_orig :: t_d ++ t_orig)).
        change (O_event outs :: t_d ++ e_orig :: t_orig)
          with ([O_event outs] ++ (t_d ++ e_orig :: t_orig)).
        pose proof (output_in_trace_app x [O_event outs] (e_orig :: t_d ++ t_orig)) as H1.
        pose proof (output_in_trace_app x [O_event outs] (t_d ++ e_orig :: t_orig)) as H2.
        pose proof (output_in_trace_swap x t_d e_orig t_orig) as Hsw.
        tauto.
  Qed.

  Context (initial : state).

  Definition can_implies_will :=
    forall t s o,
      star step initial t s ->
      allowed_trace t ->
      can_output s t o ->
      will_output s t o.

  Definition can_implies_will' :=
    forall t s o,
      star step initial t s ->
      allowed_trace t ->
      output_in_trace o t ->
      forall s' t',
        incl (inputs_of t) (inputs_of t') ->
        star step initial t' s' ->
        allowed_trace t' ->
        will_output s' t' o.

  Lemma can_output_step_preserved :
    can_implies_will ->
    (forall t, allowed t) ->
    forall ns tau e ns' o,
      star step initial tau ns ->
      step ns e ns' ->
      can_output ns tau o ->
      can_output ns' (e :: tau) o.
  Proof.
    intros Hciw A_univ ns tau e ns' o Hstar Hstep Hcan.
    apply will_implies_can; [unfold allowed_trace; auto|].
    apply (will_output_step A_univ ns e ns' tau o Hstep).
    apply Hciw; [exact Hstar | unfold allowed_trace; auto | exact Hcan].
  Qed.

  Definition monotone :=
    forall t1 t2 s1 s2 o,
      star step initial t1 s1 ->
      star step s1 t2 s2 ->
      allowed_trace t1 ->
      allowed_trace (t2 ++ t1) ->
      can_output s1 t1 o ->
      can_output s2 (t2 ++ t1) o.

  Definition monotone' :=
    forall t1 t2 s1 s2 o,
      star step initial t1 s1 ->
      star step initial t2 s2 ->
      allowed_trace t1 ->
      allowed_trace t2 ->
      incl (inputs_of t1) (inputs_of t2) ->
      can_output s1 t1 o ->
      can_output s2 t2 o.

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
        assert (HallT : allowed_trace T).
        { unfold allowed_trace in *. subst T.
          rewrite inputs_of_app, Hinp_a, app_nil_r. exact Hall. }
        assert (HoutT : output_in_trace o T).
        { subst T. apply output_in_trace_app.
          apply output_in_trace_app in Hout as [Hout|Hout]; [right|left]; exact Hout. }
        apply (Hciw' T s_f o Hstar_T HallT HoutT s t); auto.
        subst T. rewrite inputs_of_app, Hinp_a, app_nil_r.
        apply incl_refl.
      + (* monotone' *)
        intros t1 t2 s1 s2 o Hstar1 Hstar2 Hall1 Hall2 Hincl Hcan1.
        destruct Hcan1 as (T_a & s_f & Hstar_a & Hinp_a & Hout).
        pose proof (star_app _ _ _ _ _ _ Hstar1 Hstar_a) as Hstar_T.
        set (T := t1 ++ T_a) in *.
        assert (HallT : allowed_trace T).
        { unfold allowed_trace in *. subst T.
          rewrite inputs_of_app, Hinp_a, app_nil_r. exact Hall1. }
        assert (HoutT : output_in_trace o T).
        { subst T. apply output_in_trace_app.
          apply output_in_trace_app in Hout as [Hout|Hout]; [right|left]; exact Hout. }
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
    inversion Hcan as [HP | midset Hcan_step Hmid]; clear Hcan; subst.
    - exists [], s2. split; [constructor|].
      split; [reflexivity|].
      cbn. apply output_in_trace_app. right. exact HP.
    - cbv [can_step] in Hcan_step.
      specialize (Hcan_step _ _ Hstar2 Hallt).
      destruct Hcan_step as [Hmid_left | (s'' & outs & Hstep & Hmidset)].
      + exact (will_implies_can _ _ _ Hallt (Hmid _ Hmid_left)).
      + specialize (Hmid _ Hmidset).
        assert (Hall' : allowed_trace (O_event outs :: t2 ++ t1)).
        { unfold allowed_trace. cbn. exact Hallt. }
        apply (will_implies_can _ _ _ Hall') in Hmid.
        destruct Hmid as (t' & s''' & Hstar' & Hinp' & Hout').
        exists (O_event outs :: t'), s'''.
        split; [econstructor; eassumption|].
        split; [cbn; exact Hinp'|].
        cbn. apply output_in_trace_swap. exact Hout'.
  Qed.

  Context (D : list message -> message -> Prop).

  Definition complete :=
    forall t s,
      star step initial t s ->
      allowed_trace t ->
      forall output,
        D (inputs_of t) output ->
        will_output s t output.

  Definition sound :=
    forall t s,
      star step initial t s ->
      allowed_trace t ->
      forall output,
        output_in_trace output t ->
        D (inputs_of t) output.

  Definition described_by := sound /\ complete.

  Definition complete_weak :=
    forall t s,
      star step initial t s ->
      allowed_trace t ->
      forall output,
        D (inputs_of t) output ->
        can_output s t output.

  Definition described_by_weak := sound /\ complete_weak.

  Lemma complete_weak_implies_strong :
    complete_weak ->
    can_implies_will ->
    complete.
  Proof.
    intros Hweak Hcan t s Hstar Hall o HD.
    apply Hcan; auto.
  Qed.
End __.
