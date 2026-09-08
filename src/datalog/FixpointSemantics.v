(*usually, we work with proof-tree semantics.
  here we prove them equivalent to some fixpoint semantics, which used to be used in the currently-broken QueryableToRunnable.v but are not currently used for anything.
 *)

From Stdlib Require Import List.
From coqutil Require Import Tactics.fwd.
From Datalog.Util Require Import Tactics Fp List Pftree.
From Datalog Require Import Datalog.
Import ListNotations.

Section __.
  Context {fact rule meta_fact normal_fact : Type}.
  Context {one_step_derives : list rule -> list meta_fact -> normal_fact -> Prop}.
  Context {rule_impl :
            (list meta_fact -> normal_fact -> Prop) -> rule -> fact -> list fact -> Prop}.
  Context {prog_impl : list rule -> (fact -> Prop) -> fact -> Prop}.

  Definition F p Q Px :=
    let '(P, x) := Px in
    P x \/ Q (P, x) \/ exists hyps', Exists (fun r => rule_impl (one_step_derives p) r x hyps') p /\ Forall (fun x => Q (P, x)) hyps'.

  Lemma F_mono p S1 S2 :
    (forall x, S1 x -> S2 x) ->
    (forall x, F p S1 x -> F p S2 x).
  Proof.
    cbv [F]. intros Hle [P x] H. intuition auto. fwd. eauto 8.
  Qed.

  Definition S_sane {U : Type} (S : (U -> Prop) * U -> Prop) :=
    (forall P x, P x -> S (P, x)) /\
      (forall P1 x P2,
          S (P1, x) ->
          (forall y, P1 y -> S (P2, y)) ->
          S (P2, x)).

  Lemma prog_impl_lfp p :
    equiv (fun '(P, f) => prog_impl p P f) (lfp (F p)).
  Proof.
    cbv [equiv]. intros. cbv [prog_impl].
    epose proof pftree_lfp as H. cbv [equiv] in H. rewrite H.
    cbv [F]. reflexivity.
  Qed.

  Lemma S_sane_ext {U : Type} (P Q : (U -> Prop) * U -> Prop) :
    equiv P Q ->
    S_sane P ->
    S_sane Q.
  Proof.
    cbv [equiv S_sane]. intros.
    assert ((forall x, P x -> Q x) /\ (forall x, Q x -> P x)) by (split; intros; apply H; assumption).
    fwd. eauto 9.
  Qed.

  Hint Unfold prog_impl : core.

  Lemma S_sane_lfp p : S_sane (lfp (F p)).
  Proof.
    eapply S_sane_ext; [apply prog_impl_lfp|]. cbv [S_sane]. split; intros; eauto.
    Fail Fail solve [induction H; eauto].
    eapply pftree_trans. eapply pftree_weaken_hyp; eauto.
  Qed.

  (*this gets more complicated due to meta rules :((( *)
  Lemma split_fixpoint (p : list rule) S :
    (forall P x, P x -> S (P, x)) ->
    (forall r, In r p -> fp (F [r]) S) <->
      fp (F p) S.
  Proof.
    intros Sgood1. cbv [fp F]. split.
    - intros H [P x] Hx. destruct Hx as [Hx| [Hx|Hx]]; eauto.
      fwd. apply Exists_exists in Hxp0. fwd. eapply H; eauto 6. admit.
    - intros H r Hr [P x] Hx. destruct Hx as [Hx| [Hx|Hx]]; eauto. fwd.
      invert_list_stuff.
      apply H. right. right. eexists. split; [|eassumption]. apply Exists_exists. eauto.
      admit.
  Abort.
End __.
