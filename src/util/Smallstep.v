(*worth comparing to https://compcert.org/doc/html/compcert.common.Smallstep.html*)
From Stdlib Require Import List.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
Import ListNotations.

Section io.
  Context {message : Type}.

  Variant IO_event : Type :=
    | I_event : message -> IO_event
    | O_event : list message -> IO_event.

  Definition inputs_of (t : list IO_event) :=
    flat_map (fun e => match e with I_event m => [m] | _ => [] end) t.

  Definition output_in_trace (output : message) (t : list IO_event) :=
    exists outs, In (O_event outs) t /\ In output outs.

  Definition event_guaranteed (e : IO_event) :=
    match e with
    | O_event _ => True
    | I_event _ => False
    end.

  Context {state : Type}.
  Context (recv : state -> message -> state).
  Context (emit : state -> list message -> state -> Prop).

  Definition step : state -> IO_event -> state -> Prop :=
    fun s ev s' =>
      match ev with
      | I_event m  => s' = recv s m
      | O_event ms => emit s ms s'
      end.
End io.

Arguments IO_event : clear implicits.

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

  Lemma inputs_of_event_guaranteed (t : list (IO_event message)) :
    Forall event_guaranteed t -> inputs_of t = [].
  Proof.
    induction 1; auto.
    destruct x; cbn; auto. contradiction.
  Qed.

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

  (*the angel can step to the postcondition regardless of the demon's actions*)
  Definition can_step '(s, t) (P : state * list (IO_event message) -> Prop) : Prop :=
    forall s' t',
      star step s t' s' ->
      allowed_trace (t' ++ t) ->
      exists s'' outs,
        step s' (O_event outs) s'' /\
          P (s'', O_event outs :: t' ++ t).

  Lemma eventually_can_step_to_star :
    forall (P : state * list (IO_event message) -> Prop) s t,
      allowed_trace t ->
      eventually can_step P (s, t) ->
      exists s' tr,
        star step s tr s' /\
        Forall event_guaranteed tr /\
        P (s', rev tr ++ t).
  Proof.
    intros P s0 t0 Hallow Hwill.
    remember (s0, t0) as st eqn:Est.
    revert s0 t0 Hallow Est.
    induction Hwill as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
      intros s0 t0 Hallow [= -> ->].
    - exists s0, []. split; [constructor|]. split; [constructor|exact HP].
    - destruct (Hcan s0 [] (star_refl _ _)) as (s'' & outs & Hstep & Hmidset).
      { cbn. exact Hallow. }
      assert (Hallow' : allowed_trace (O_event outs :: t0)).
      { unfold allowed_trace. cbn. exact Hallow. }
      destruct (IH _ Hmidset s'' (O_event outs :: t0) Hallow' eq_refl)
        as (s_final & tr & Hstar & Hguar & HP).
      exists s_final, (O_event outs :: tr).
      split; [econstructor; eassumption|].
      split; [constructor; [exact I|exact Hguar]|].
      cbn. rewrite <- app_assoc. cbn. exact HP.
  Qed.

  Definition can_output start t output :=
    exists t' s',
      star step start t' s' /\
        Forall event_guaranteed t' /\
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
      split; [constructor|exact HP].
    - cbv [can_step] in Hcan.
      specialize (Hcan s0 [] (star_refl _ _)).
      cbn in Hcan. specialize (Hcan Hall).
      destruct Hcan as (s'' & outs & Hstep & Hmidset).
      assert (Hall' : allowed_trace (O_event outs :: t0)).
      { unfold allowed_trace. cbn. exact Hall. }
      destruct (IH _ Hmidset s'' (O_event outs :: t0) Hall' eq_refl)
        as (t'' & s''' & Hstar'' & Hforall'' & Hout'').
      exists (O_event outs :: t''), s'''.
      split; [econstructor; eassumption|].
      split; [constructor; [exact I|exact Hforall'']|].
      cbn. apply output_in_trace_swap. exact Hout''.
  Qed.

  Context (initial : state).

  Definition can_implies_will :=
    forall t s o,
      star step initial t s ->
      allowed_trace t ->
      can_output s t o ->
      will_output s t o.

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
      incl (inputs_of t1) (inputs_of t2) ->
      can_output s1 t1 o ->
      can_output s2 t2 o.

  Lemma ciw_monotone :
    can_implies_will -> monotone.
  Proof.
    cbv [can_implies_will monotone].
    intros Hciw t1 t2 s1 s2 o Hstar1 Hstar2 Hall1 Hallt Hcan.
    apply (Hciw _ _ _ Hstar1 Hall1) in Hcan.
    cbv [will_output] in Hcan.
    inversion Hcan as [HP | midset Hcan_step Hmid]; clear Hcan; subst.
    - exists [], s2. split; [constructor|].
      split; [constructor|].
      cbn. apply output_in_trace_app. right. exact HP.
    - cbv [can_step] in Hcan_step.
      specialize (Hcan_step _ _ Hstar2 Hallt).
      destruct Hcan_step as (s'' & outs & Hstep & Hmidset).
      specialize (Hmid _ Hmidset).
      assert (Hall' : allowed_trace (O_event outs :: t2 ++ t1)).
      { unfold allowed_trace. cbn. exact Hallt. }
      apply (will_implies_can _ _ _ Hall') in Hmid.
      destruct Hmid as (t' & s''' & Hstar' & Hforall' & Hout').
      exists (O_event outs :: t'), s'''.
      split; [econstructor; eassumption|].
      split; [constructor; [exact I|exact Hforall']|].
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
