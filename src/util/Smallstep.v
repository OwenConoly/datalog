(*worth comparing to https://compcert.org/doc/html/compcert.common.Smallstep.html*)
From Stdlib Require Import List.
From coqutil Require Import Semantics.OmniSmallstepCombinators.
Import ListNotations.
Section __.
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
End __.

Section __.
  Context {state event : Type}.
  Context (step : state -> event -> state -> Prop).
  Context (allowed : list event -> Prop).
  Context (guaranteed : list event -> event -> Prop).

  (*the angel can step to the postcondition regardless of the demon's actions*)
  Definition can_step '(s, t) (P : state * list event -> Prop) : Prop :=
    forall s' t',
      star step s t' s' ->
      allowed (t' ++ t) ->
      exists s'' e,
        guaranteed (t' ++ t) e /\
          step s' e s'' /\
          P (s'', e :: t' ++ t).

  Lemma eventually_can_step_to_star :
    forall (P : state * list event -> Prop) s t,
      (forall t', allowed (t' ++ t)) ->
      eventually (can_step) P (s, t) ->
      exists s' tr, star step s tr s' /\ P (s', rev tr ++ t).
  Proof.
    intros P s0 t0 Hallow Hwill.
    remember (s0, t0) as st eqn:Est.
    revert s0 t0 Hallow Est.
    induction Hwill as [[s' t'] HP | [s' t'] midset Hcan Hmid IH];
      intros s0 t0 Hallow [= -> ->].
    - exists s0, []. split; [constructor|exact HP].
    - destruct (Hcan s0 [] (star_refl _ _) (Hallow _))
        as (s'' & e & _ & Hstep & Hmidset).
      destruct (IH (s'', e :: t0) Hmidset s'' (e :: t0)) as (s_final & tr & Hstar & HP).
      { intros t''. specialize (Hallow (t'' ++ [e])).
        rewrite <- app_assoc in Hallow. exact Hallow. }
      { reflexivity. }
      exists s_final, (e :: tr). split; [econstructor; eassumption|].
      cbn. rewrite <- app_assoc. exact HP.
  Qed.
End __.
