From coqutil Require Import Semantics.OmniSmallstepCombinators.
From Datalog Require Import Relations.

Section step.
  Context {state label : Type}.
  Context (step : state -> label -> state -> Prop).

  Definition any_step s s' := exists lbl, step s lbl s'.

  Definition will_step s (P : state -> Prop) : Prop :=
    exists lbl,
    forall s',
      any_step^* s s' ->
      P s' \/ exists s'', step s' lbl s'' /\ P s''.

  Lemma will_step_impl (P Q : state -> Prop) s :
    will_step s P ->
    (forall x, P x -> Q x) ->
    will_step s Q.
  Proof.
    intros [lbl H] HPQ. exists lbl. intros s' Hs'.
    destruct (H s' Hs') as [HP | (s'' & Hstep & HP)].
    - left. apply HPQ, HP.
    - right. exists s''. split; [ exact Hstep | apply HPQ, HP ].
  Qed.

  Lemma will_step_reach (P : state -> Prop) s :
    will_step s (fun s' => any_step^* s s' -> P s') ->
    will_step s P.
  Proof.
    intros [lbl H]. exists lbl. intros s' Hs'.
    destruct (H s' Hs') as [HP | (s'' & Hstep & HP)].
    - left. auto.
    - right. exists s''. split; [ exact Hstep | ].
      apply HP. eapply crt1n_trans_compose; [ exact Hs' | ].
      econstructor.
      + exists lbl. exact Hstep.
      + constructor.
  Qed.

  Lemma eventually_and_reach (P : state -> Prop) s :
    eventually will_step P s ->
    eventually will_step (fun s' => any_step^* s s' /\ P s') s.
  Proof.
    intros Hev.
    enough (forall s', any_step^* s s' -> eventually will_step P s' ->
                       eventually will_step (fun s'' => any_step^* s s'' /\ P s'') s') as H.
    { apply H; [ constructor | exact Hev ]. }
    clear Hev. intros s' Hr Hev. revert Hr.
    induction Hev; intros Hr.
    - apply eventually_done. auto.
    - apply eventually_step with (midset := fun mid => midset mid /\ any_step^* s mid).
      + apply will_step_reach. eapply will_step_impl; [ eassumption | ].
        intros s'' ? ?. split; eauto using crt1n_trans_compose.
      + intros mid []. auto.
  Qed.
End step.
