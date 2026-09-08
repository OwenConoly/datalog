(*usually, we work with proof-tree semantics.
  here we prove them equivalent to some fixpoint semantics, which used to be used in the currently-broken QueryableToRunnable.v but are not currently used for anything.
 *)

From Stdlib Require Import List.
From coqutil Require Import Tactics.fwd.
From Datalog.Util Require Import Tactics Fp List Pftree.
From Datalog Require Import Datalog.
Import ListNotations.

Section __.
  Context `{params : datalog_params}.

  Definition F (p : program) Q Px :=
    let '(P, x) := Px in
    P x \/ Q (P, x) \/
      exists hyps, program.interp_step p x hyps /\ Forall (fun y => Q (P, y)) hyps.

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

  Lemma interp_lfp p :
    equiv (fun '(P, f) => program.interp p P f) (lfp (F p)).
  Proof.
    cbv [equiv]. intros. epose proof pftree.equiv_lfp as H. cbv [equiv] in H.
    rewrite H. cbv [F]. reflexivity.
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

  Lemma S_sane_lfp p : S_sane (lfp (F p)).
  Proof.
    eapply S_sane_ext; [apply interp_lfp|]. cbv [S_sane]. split; intros; eauto.
    eapply pftree.trans. eapply pftree.weaken_hyp; eauto.
  Qed.

  (*this gets more complicated due to meta rules :((( *)
  Lemma split_fixpoint (p : program) S :
    (forall P x, P x -> S (P, x)) ->
    (forall r, In r p.(program.rules) ->
        fp (F {| program.rules := [r]; program.meta_rules := [] |}) S) <->
      fp (F p) S.
  Proof. Abort.
End __.
