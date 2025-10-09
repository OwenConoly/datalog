From Stdlib Require Import Lists.List.
From ATL Require Import ATL Map Sets FrapWithoutSets Div Tactics.
From Lower Require Import ListMisc.
From coqutil Require Import Datatypes.List Tactics.fwd Tactics.destr.
Require Import Datalog.Tactics.

Import ListNotations.
Section subset.
Context {A : Type}.
Context (eqb : A -> A -> bool) {eqb_spec :  forall x0 y0 : A, BoolSpec (x0 = y0) (x0 <> y0) (eqb x0 y0)}.

(*I would like to do some magic to make this infer the eqb to use, but idk how*)
(*hmm i am making my compiler take quadratic time.  i guess it already did though.*)
Definition subsetb (l1 l2 : list A) :=
  forallb (fun x => existsb (eqb x) l2) l1.

Definition subset (l1 l2 : list A) :=
  (forall a, In a l1 -> In a l2).

Lemma Forall_subset P l1 l2 :
  Forall P l2 ->
  subset l1 l2 ->
  Forall P l1.
Proof. do 2 rewrite Forall_forall. auto. Qed.

Lemma subsetb_subset l1 l2 :
  subsetb l1 l2 = true <-> subset l1 l2.
Proof.
  cbv [subsetb]. rewrite forallb_forall. split.
  - intros H a H0. apply H in H0. rewrite existsb_exists in H0. fwd. auto.
  - intros. rewrite existsb_exists. eexists ?[x0]. destr (eqb x ?x0); eauto.
Qed.

Lemma subset_refl x : subset x x.
Proof. cbv [subset]. auto. Qed.

Lemma subset_trans x y z :
  subset x y ->
  subset y z ->
  subset x z.
Proof. cbv [subset]. auto. Qed.

Lemma subset_app_app x1 y1 x2 y2 :
  subset x1 x2 ->
  subset y1 y2 ->
  subset (x1 ++ y1) (x2 ++ y2).
Proof. cbv [subset]. intros. repeat rewrite in_app_iff in *. intuition auto. Qed.
End subset.

Section Forall.
Context {A B : Type}.
Implicit Type xs : list A.
Implicit Type ys : list B.

Lemma Forall2_forget_l R xs ys :
  Forall2 R xs ys ->
  Forall (fun y => exists x, In y ys /\ R x y) ys.
Proof.
  induction 1; eauto. simpl. econstructor; eauto.
  eapply Forall_impl; [|eassumption]. simpl. intros. fwd. eauto.
Qed.

Lemma Forall2_forget_r R xs ys :
  Forall2 R xs ys ->
  Forall (fun x => exists y, In y ys /\ R x y) xs.
Proof.
  induction 1; eauto. simpl. econstructor; eauto.
  eapply Forall_impl; [|eassumption]. simpl. intros. fwd. eauto.
Qed.

Lemma Forall_exists_r_Forall2 R xs :
  Forall (fun x => exists y, R x y) xs ->
  exists ys, Forall2 R xs ys.
Proof. induction 1; fwd; eauto. Qed.

Lemma Forall2_unique_r R xs ys ys' :
  Forall2 R xs ys ->
  Forall2 R xs ys' ->
  (forall x y y', R x y -> R x y' -> y = y') ->
  ys = ys'.
Proof.
  intros H. revert ys'. induction H; intros; invert_list_stuff; f_equal; eauto.
Qed.

Lemma Forall2_and R1 R2 xs ys :
  Forall2 R1 xs ys ->
  Forall2 R2 xs ys ->
  Forall2 (fun x y => R1 x y /\ R2 x y) xs ys.
Proof. induction 1; intros; invert_list_stuff; eauto. Qed.

Lemma Forall2_true xs ys :
  length xs = length ys ->
  Forall2 (fun _ _ => True) xs ys.
Proof. revert ys. induction xs; destruct ys; simpl; try congruence; eauto. Qed.

Lemma in_combine_l_iff xs ys x (y : B) :
  (exists y, In (x, y) (combine xs ys)) <-> In x (firstn (length ys) xs).
Proof.
  revert ys. induction xs; simpl; intros; eauto.
  - destruct (length _); simpl; split; intros; fwd; eauto.
  - destruct ys; simpl; split; intros; fwd; eauto.
    + destruct H; fwd; eauto. rewrite <- IHxs. eauto.
    + destruct H; subst; fwd; eauto. rewrite <- IHxs in H. fwd. eauto.
Qed.
End Forall.

Section misc.
Context {A : Type}.
Implicit Type xs : list A.  

Lemma invert_concat_same xss xss' :
  concat xss = concat xss' ->
  Forall2 (fun xs xs' => length xs = length xs') xss xss' ->
  xss = xss'.
Proof.
  induction 2; simpl in *; eauto. eapply invert_app in H; eauto.
  fwd. f_equal. eauto.
Qed.

Lemma invert_concat_same' xss xss' n :
  concat xss = concat xss' ->
  length xss = length xss' ->
  Forall (fun xs => length xs = n) xss ->
  Forall (fun xs => length xs = n) xss' ->
  xss = xss'.
Proof.
  intros H H0 H1 H2. apply invert_concat_same; auto.
  eapply Forall2_impl_strong; [|apply Forall2_true; auto].
  intros x y _ Hx Hy. rewrite Forall_forall in *. rewrite H1, H2; auto.
Qed.
End misc.
