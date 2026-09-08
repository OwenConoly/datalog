From Stdlib Require Import List.
From Datalog.Util Require Import Tactics Fp List.
From coqutil Require Import Tactics.fwd.

Module pftree.
  Section __.
    Context {T : Type}.
    Implicit Type P : T -> list T -> Prop.

    Unset Elimination Schemes.
    Inductive pftree (P : T -> list T -> Prop) (Q : T -> Prop) : T -> Prop :=
    | leaf x :
      Q x ->
      pftree _ _ x
    | step x l :
      P x l ->
      Forall (pftree _ _) l ->
      pftree _ _ x.
    Set Elimination Schemes.
    #[local] Hint Constructors pftree : core.

    Lemma ind P Q R :
      (forall x, Q x -> R x) ->
      (forall x l,
          P x l ->
          Forall (pftree P Q) l ->
          Forall R l ->
          R x) ->
      forall x, pftree P Q x -> R x.
    Proof.
      intros H1 H2. fix self 2.
      intros x Hx. invert Hx. 1: auto. eapply H2. 1,2: eassumption.
      clear -H0 self. induction H0; eauto.
    Qed.
    Register Scheme ind as ind_nodep for pftree.

    Lemma trans P x Q :
      pftree P (pftree P Q) x ->
      pftree P Q x.
    Proof. induction 1; eauto. Qed.

    Lemma weaken_hyp P x Q1 Q2 :
      pftree P Q1 x ->
      (forall y, Q1 y -> Q2 y) ->
      pftree P Q2 x.
    Proof. intros H1 H2. induction H1; eauto. Qed.

    Lemma invariant P Q x Inv :
      Inv x ->
      (forall y l, Inv y -> P y l -> Forall Inv l) ->
      pftree P Q x ->
      pftree P (fun y => Q y /\ Inv y) x.
    Proof.
      intros Hx Hclosed Htree. setoid_rewrite Forall_forall in Hclosed.
      revert Hx. induction Htree; auto.
      intros. eapply step; [eassumption|]. rewrite Forall_forall in *. eauto 6.
    Qed.

    (*TODO make this look nicer?*)
    Lemma equiv_lfp P :
      equiv (fun '(Q0, x) => pftree P Q0 x)
        (lfp (fun Q '(Q0, x) => Q0 x \/ Q (Q0, x) \/ exists l, P x l /\ Forall (fun y => Q (Q0, y)) l)).
    Proof.
      cbv [equiv lfp fp]. intros [Q0 x]. split; intros; fwd.
      - apply H0. induction H; eauto.
        right. right. exists l. split; [assumption|]. eapply Forall_impl; [eassumption|].
        simpl. intros y. apply (H0 (_, _)).
      - apply (H (fun '(Q, x) => _)). clear. intros [Q x]. intros [Hx| [Hx |Hx] ]; eauto.
        fwd. eapply step; eassumption.
    Qed.

    Lemma weaken (P1 P2 : T -> list T -> Prop) Q x :
      pftree P1 Q x ->
      (forall y l, P1 y l -> P2 y l) ->
      pftree P2 Q x.
    Proof. induction 1; eauto. Qed.

    Lemma step_ext (P1 P2 : T -> list T -> Prop) Q x :
      (forall y l, P1 y l <-> P2 y l) ->
      pftree P1 Q x <-> pftree P2 Q x.
    Proof.
      intros H. split; intros Htree.
      - eapply weaken; [exact Htree | intros y l Hyl; apply H; exact Hyl].
      - eapply weaken; [exact Htree | intros y l Hyl; apply H; exact Hyl].
    Qed.

    Lemma hyp_ext P f Q1 Q2 :
      (forall f', Q1 f' <-> Q2 f') ->
      pftree P Q1 f <-> pftree P Q2 f.
    Proof. eauto using weaken_hyp. Qed.

    Lemma stratify (P1 P2 : T -> list T -> Prop) Q x :
      (forall y l z l', P2 y l -> In z l -> ~ P1 z l') ->
      pftree (fun y l => P1 y l \/ P2 y l) Q x ->
      pftree P1 (pftree P2 Q) x.
    Proof.
      intros Hsep Htree. induction Htree; auto. destruct H.
      - eapply step; eassumption.
      - apply leaf. eapply step; [eassumption|].
        rewrite Forall_forall in *. intros z Hz. specialize (H1 z Hz).
        invert H1; [assumption|]. exfalso. eapply Hsep; eassumption.
    Qed.

    Lemma unstratify (P1 P2 : T -> list T -> Prop) Q x :
      pftree P1 (pftree P2 Q) x ->
      pftree (fun y l => P1 y l \/ P2 y l) Q x.
    Proof. eauto 7 using weaken, trans, weaken_hyp. Qed.

    Lemma pftree_stratify_iff (P1 P2 : T -> list T -> Prop) Q x :
      (forall y l z l', P2 y l -> In z l -> ~ P1 z l') ->
      pftree (fun y l => P1 y l \/ P2 y l) Q x <-> pftree P1 (pftree P2 Q) x.
    Proof. auto using stratify, unstratify. Qed.
  End __.
End pftree. Export pftree (pftree).
#[export] Hint Constructors pftree : core.
