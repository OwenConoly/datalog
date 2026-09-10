From Stdlib Require Import List.
From Datalog.Util Require Import Tactics Fp List.
From coqutil Require Import Tactics.fwd.
Import ListNotations.

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

    Lemma invert P Q x :
      pftree P Q x ->
      Q x \/ exists l, P x l /\ Forall (pftree P Q) l.
    Proof. invert 1; eauto. Qed.

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

    Lemma trim_leaves P Q x :
      pftree P Q x ->
      pftree P (fun y => Q y /\ (y = x \/ exists z l, P z l /\ In y l)) x.
    Proof.
      intros. eapply invariant with (Inv := fun y => y = x \/ exists z l, P z l /\ In y l).
      - auto.
      - intros. rewrite Forall_forall. intros. right. eauto.
      - assumption.
    Qed.

    Definition F P Q Px :=
      let '(Q0, x) := Px in
      Q0 x \/ Q (Q0, x) \/ exists l, P x l /\ Forall (fun y => Q (Q0, y)) l.

    Lemma equiv_lfp P :
      equiv (fun '(Q0, x) => pftree P Q0 x) (lfp (F P)).
    Proof.
      cbv [equiv lfp fp F]. intros [Q0 x]. split; intros; fwd.
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

    Lemma stratify_iff (P1 P2 : T -> list T -> Prop) Q x :
      (forall y l z l', P2 y l -> In z l -> ~ P1 z l') ->
      pftree (fun y l => P1 y l \/ P2 y l) Q x <-> pftree P1 (pftree P2 Q) x.
    Proof. auto using stratify, unstratify. Qed.

    (*a linearized proof tree: each element is a leaf, or steps into elements later in the list*)
    Inductive flat P (Q : T -> Prop) : list T -> Prop :=
    | flat_nil : flat _ _ []
    | flat_cons x xs :
      Q x \/ (exists l, P x l /\ incl l xs) ->
      flat _ _ xs ->
      flat _ _ (x :: xs).
    #[local] Hint Constructors flat : core.

    Lemma flat_app P Q xs1 xs2 :
      flat P Q xs1 ->
      flat P Q xs2 ->
      flat P Q (xs1 ++ xs2).
    Proof.
      induction 1; simpl; auto. intros. constructor; auto.
      destruct H; fwd; eauto 6 with incl.
    Qed.

    Lemma flat_concat P Q xss :
      Forall (flat P Q) xss ->
      flat P Q (concat xss).
    Proof. induction 1; simpl; auto using flat_app. Qed.

    Lemma exists_flat P Q x :
      pftree P Q x ->
      exists xs, flat P Q xs /\ In x xs.
    Proof.
      induction 1.
      - exists [x]. simpl. auto.
      - apply Forall_exists_r_Forall2 in H1. fwd.
        exists (x :: concat ys). simpl. split; auto. constructor.
        + right. eexists. split; [eassumption|].
          apply Forall2_forget_r in H1. cbv [incl]. apply Forall_forall.
          eapply Forall_impl; [eassumption|].
          simpl. intros. fwd. rewrite in_concat. eauto.
        + apply flat_concat.
          apply Forall2_forget_l in H1. eapply Forall_impl; [eassumption|].
          simpl. intros. fwd. assumption.
    Qed.

    Lemma flat_pftree P Q xs :
      flat P Q xs ->
      Forall (pftree P Q) xs.
    Proof.
      induction 1; constructor; auto.
      destruct H; fwd; auto.
      eapply step; [eassumption|]. eauto using incl_Forall.
    Qed.

    Lemma flat_forall_step P Q xs :
      flat P Q xs ->
      Forall (fun x => Q x \/ exists l, P x l /\ incl l xs) xs.
    Proof.
      induction 1; auto. constructor.
      - destruct H; fwd; auto. right. eexists. split; [eassumption|].
        auto with incl.
      - eapply Forall_impl; [eassumption|]. simpl. intros ? [?|?]; fwd; eauto 6 with incl.
    Qed.

    #[local] Hint Unfold In : core.

    (*this is a lemma about pairwise properties, because that is all that i need to reason about.
      it is also true for n-wise properties, or even properties of arbitrary-length finite lists.
      it is not true for infinite sets. *)
    Lemma pairwise_ind' P Q (R : T -> T -> Prop) :
      (forall x1 x2, R x1 x2 <-> R x2 x1) ->
      (forall x xs,
          (forall y1 y2, In y1 xs -> In y2 xs -> R y1 y2) ->
          Forall (pftree P Q) (x :: xs) ->
          Forall (fun y => Q y \/ exists l, P y l /\ incl l xs) (x :: xs) ->
          Forall (R x) (x :: xs)) ->
      forall xs,
        flat P Q xs ->
        forall x1 x2,
          In x1 xs ->
          In x2 xs ->
          R x1 x2.
    Proof.
      intros Hcomm Hstep xs Hxs.
      induction Hxs as [|x xs Hx Hxs IH].
      - simpl. contradiction.
      - assert (Hall: Forall (R x) (x :: xs)).
        { apply Hstep.
          - assumption.
          - apply flat_pftree. constructor; assumption.
          - constructor; auto using flat_forall_step. }
        rewrite Forall_forall in Hall.
        intros x1 x2 [H1|H1] [H2|H2]; subst; auto.
        apply Hcomm. auto.
    Qed.

    Lemma pairwise_ind P Q (R : T -> T -> Prop) :
      (forall x1 x2, R x1 x2 <-> R x2 x1) ->
      (forall x xs,
          (forall y1 y2, In y1 xs -> In y2 xs -> R y1 y2) ->
          Forall (pftree P Q) (x :: xs) ->
          Forall (fun y => Q y \/ exists l, P y l /\ incl l xs) (x :: xs) ->
          Forall (R x) (x :: xs)) ->
      forall x1 x2,
        pftree P Q x1 ->
        pftree P Q x2 ->
        R x1 x2.
    Proof.
      intros ? ? x1 x2 H1 H2. apply exists_flat in H1, H2.
      fwd. eapply flat_app in H1p0; [|exact H2p0].
      eapply pairwise_ind'; try eassumption.
      1,2: apply in_app_iff; auto.
    Qed.
  End __.
End pftree. Export pftree (pftree).
#[export] Hint Constructors pftree : core.
