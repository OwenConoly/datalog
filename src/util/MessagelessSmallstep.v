From coqutil Require Import Semantics.OmniSmallstepCombinators.
From Stdlib Require Import List.
From Datalog Require Import Relations Tactics.

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

  Lemma any_step_star_snoc s s' lbl s'' :
    any_step^* s s' ->
    step s' lbl s'' ->
    any_step^* s s''.
  Proof.
    intros Hs' Hstep. eapply crt1n_trans_compose; [ exact Hs' | ].
    econstructor.
    - exists lbl. exact Hstep.
    - constructor.
  Qed.

  Lemma will_step_reach (P : state -> Prop) s :
    will_step s (fun s' => any_step^* s s' -> P s') ->
    will_step s P.
  Proof.
    intros [lbl H]. exists lbl. intros s' Hs'.
    destruct (H s' Hs') as [HP | (s'' & Hstep & HP)].
    - left. auto.
    - right. exists s''. split; [ exact Hstep | ].
      eauto using any_step_star_snoc.
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

  Definition ev_stable (P : state -> Prop) : Prop :=
    forall s lbl s', P s -> step s lbl s' -> P s'.

  Lemma ev_stable_star P s s' :
    ev_stable P ->
    any_step^* s s' ->
    P s ->
    P s'.
  Proof. intros Hst Hstar. induction Hstar; [ auto | ]. destruct H. eauto. Qed.

  Lemma eventually_will_step_advance Q s s' :
    ev_stable Q ->
    any_step^* s s' ->
    eventually will_step Q s ->
    eventually will_step Q s'.
  Proof.
    intros Hstable Hstar Hev. destruct Hev as [HQ | midset [lbl Hstep] Hnext].
    - apply eventually_done. eapply ev_stable_star; eassumption.
    - apply eventually_step with (midset := midset); [ | assumption ].
      exists lbl. intros s'' Hs''. apply Hstep. eapply crt1n_trans_compose; eassumption.
  Qed.

  Lemma eventually_carry_stable_gen P Q s :
    ev_stable P ->
    P s ->
    eventually will_step Q s ->
    eventually will_step (fun x => P x /\ Q x) s.
  Proof.
    intros Hstable HP Hev. revert HP. induction Hev; intros HP.
    - apply eventually_done. auto.
    - apply eventually_step_cps. destruct H as [lbl H]. exists lbl. intros s' Hs'.
      assert (HP' : P s') by (eapply ev_stable_star; eassumption).
      destruct (H s' Hs') as [Hleft | (s'' & Hst & Hright)].
      + left. auto.
      + right. exists s''. split; [ exact Hst | eauto ].
  Qed.

  Lemma eventually_will_step_and P Q s :
    ev_stable P ->
    ev_stable Q ->
    eventually will_step P s ->
    eventually will_step Q s ->
    eventually will_step (fun x => P x /\ Q x) s.
  Proof.
    intros HsP HsQ HevP HevQ. revert HevQ. induction HevP; intros HevQ.
    - apply eventually_carry_stable_gen; assumption.
    - apply eventually_step_cps. destruct H as [lbl H]. exists lbl. intros s' Hs'.
      destruct (H s' Hs') as [Hleft | (s'' & Hst & Hright)].
      + left. eauto using eventually_will_step_advance.
      + right. exists s''. split; [ exact Hst | ].
        eauto using eventually_will_step_advance, any_step_star_snoc.
  Qed.

  Lemma ev_stable_Forall Ps :
    Forall ev_stable Ps ->
    ev_stable (fun x => Forall (fun P => P x) Ps).
  Proof.
    intros H s lbl s' HPs Hstep. cbv beta in *. rewrite Forall_forall in *.
    intros P HP. apply (H P HP s lbl s'); [ apply HPs, HP | exact Hstep ].
  Qed.

  Lemma eventually_will_step_Forall Ps s :
    Forall ev_stable Ps ->
    Forall (fun P => eventually will_step P s) Ps ->
    eventually will_step (fun x => Forall (fun P => P x) Ps) s.
  Proof.
    intros Hst Hev. induction Hst; invert Hev.
    - apply eventually_done. constructor.
    - eapply eventually_weaken.
      + apply (eventually_will_step_and x (fun y => Forall (fun P => P y) l));
          [ assumption | apply ev_stable_Forall; assumption | assumption | auto ].
      + intros y []. constructor; assumption.
  Qed.
End step.
